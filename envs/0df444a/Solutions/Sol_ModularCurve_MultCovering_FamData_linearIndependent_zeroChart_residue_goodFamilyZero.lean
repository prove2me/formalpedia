-- Prove2me | solution 1 for ModularCurve.MultCovering.FamData.linearIndependent_zeroChart_residue_goodFamilyZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/653794bc-0461-503e-8e00-0a0105719c05

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem
import Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

namespace P2MZ5

open IsLocalRing

theorem linearIndependent_of_natRel {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type*} [Fintype ι] {μ : Type*} (v : ι → μ → k)
    (hrange : ∀ i m, ∃ n : ℕ, v i m = n)
    (hrel : ∀ n : ι → ℕ, (∀ m, ∑ i, (n i : k) * v i m = 0) → ∀ i, p ∣ n i) :
    LinearIndependent k v := by
  classical
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  rw [Fintype.linearIndependent_iff]
  intro g hg i

  refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) (g i)).mp (fun θ => ?_)

  set n : ι → ℕ := fun j => (θ (g j)).val with hn
  have hval : ∀ j, ((n j : ℕ) : ZMod p) = θ (g j) := fun j => ZMod.natCast_zmod_val _
  have hrelm : ∀ m, ∑ j, (n j : k) * v j m = 0 := by
    intro m

    choose σ hσ using fun j => hrange j m
    have hgm : ∑ j, g j * (σ j : k) = 0 := by
      have := congrFun hg m
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hσ] using this

    have hθ : ∑ j, ((σ j : ℕ) : ZMod p) * θ (g j) = 0 := by
      have h1 : θ (∑ j, ((σ j : ℕ) : ZMod p) • g j) = 0 := by
        have h2 : ∑ j, ((σ j : ℕ) : ZMod p) • g j = ∑ j, g j * (σ j : k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_natCast, mul_comm]
        rw [h2, hgm, map_zero]
      rw [map_sum] at h1
      simpa [map_smul, smul_eq_mul] using h1

    have h3 : (algebraMap (ZMod p) k) (∑ j, ((σ j : ℕ) : ZMod p) * θ (g j)) = 0 := by rw [hθ, map_zero]
    rw [map_sum] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_natCast, ← hval j, map_natCast, hσ j, mul_comm]
  have hdvd := hrel n hrelm i
  rw [← hval i]
  exact (CharP.cast_eq_zero_iff (ZMod p) p (n i)).mpr hdvd

section Rational

variable (p : ℕ) [Fact p.Prime]

abbrev Zp : ValuationSubring ℚ := (Rat.padicValuation p).valuationSubring

theorem mem_Zp_iff (x : ℚ) : x ∈ Zp p ↔ 0 ≤ padicValRat p x := by
  rw [Valuation.mem_valuationSubring_iff]
  show (if x = 0 then (0 : WithZero (Multiplicative ℤ)) else WithZero.exp (-padicValRat p x)) ≤ 1 ↔ _
  split_ifs with hx
  · simp [hx]
  · rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem natCast_mem_Zp (n : ℕ) : (n : ℚ) ∈ Zp p := by
  rw [mem_Zp_iff, padicValRat.of_nat]; exact_mod_cast Nat.zero_le _

theorem inv_mem_Zp {x : ℚ} (hv : padicValRat p x = 0) : x⁻¹ ∈ Zp p := by
  rw [mem_Zp_iff, padicValRat.inv, hv, neg_zero]

theorem p_dvd_of_pos {x : ℚ} (hx0 : x ≠ 0) (hv : 0 < padicValRat p x) :
    ∃ y : ℚ, y ∈ Zp p ∧ x = p * y := by
  refine ⟨x / p, ?_, ?_⟩
  · rw [mem_Zp_iff, padicValRat.div hx0 (by exact_mod_cast (Fact.out : p.Prime).ne_zero), padicValRat.self
      (Fact.out : p.Prime).one_lt]
    omega
  · rw [mul_div_cancel₀ _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)]

variable {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
  (hmem : ∀ x : ℚ, x ∈ Zp p → algebraMap ℚ K x ∈ A)

noncomputable def toA : ↥(Zp p) →+* ↥A where
  toFun x := ⟨algebraMap ℚ K x, hmem x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_toA (x : ↥(Zp p)) : ((toA p A hmem x : ↥A) : K) = algebraMap ℚ K x := rfl

noncomputable def red : ↥(Zp p) →+* ResidueField ↥A := (residue ↥A).comp (toA p A hmem)

theorem red_apply (x : ↥(Zp p)) : red p A hmem x = residue ↥A (toA p A hmem x) := rfl

theorem exists_eq_p_mul_of_red_eq_zero (x : ↥(Zp p)) (hx : red p A hmem x = 0) :
    ∃ y : ↥(Zp p), x = (p : ↥(Zp p)) * y := by
  by_cases hx0 : (x : ℚ) = 0
  · exact ⟨0, Subtype.ext (by simp [hx0])⟩
  have hv : 0 ≤ padicValRat p (x : ℚ) := (mem_Zp_iff p _).mp x.2
  rcases hv.lt_or_eq with hpos | hzero
  · obtain ⟨y, hy, hxy⟩ := p_dvd_of_pos p hx0 hpos
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩
  ·
    exfalso
    have hxinv : (x : ℚ)⁻¹ ∈ Zp p := inv_mem_Zp p hzero.symm
    have hunit : IsUnit x := by
      refine ⟨⟨x, ⟨(x : ℚ)⁻¹, hxinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
      · simp [hx0]
      · simp [hx0]
    have hunitA : IsUnit (toA p A hmem x) := hunit.map _
    rw [red_apply, IsLocalRing.residue_eq_zero_iff] at hx
    exact hx hunitA

theorem exists_natCast_eq_red [CharP (ResidueField ↥A) p] (x : ↥(Zp p)) : ∃ n : ℕ, red p A hmem x = n := by
  classical

  have hden : ¬ p ∣ (x : ℚ).den := Rat.padicValuation_le_one_iff.mp ((Valuation.mem_valuationSubring_iff _ _).mp x.2)
  have hdenk : ((x : ℚ).den : ResidueField ↥A) ≠ 0 := by
    intro h; exact hden ((CharP.cast_eq_zero_iff (ResidueField ↥A) p _).mp h)

  letI : Algebra (ZMod p) (ResidueField ↥A) := ZMod.algebra _ p
  set z : ZMod p := ((x : ℚ).num : ZMod p) * (((x : ℚ).den : ZMod p))⁻¹ with hz
  refine ⟨z.val, ?_⟩
  have hzk : ((z.val : ℕ) : ResidueField ↥A) = algebraMap (ZMod p) (ResidueField ↥A) z := by
    rw [← map_natCast (algebraMap (ZMod p) (ResidueField ↥A)) z.val, ZMod.natCast_zmod_val]

  have hdenZp : ((x : ℚ).den : ℚ) ∈ Zp p := natCast_mem_Zp p _
  have hnumZp : ((x : ℚ).num : ℚ) ∈ Zp p := by
    rw [mem_Zp_iff, padicValRat.of_int]; exact_mod_cast Nat.zero_le _
  have hkey : red p A hmem x * ((x : ℚ).den : ResidueField ↥A) = ((x : ℚ).num : ResidueField ↥A) := by
    have h1 : x * (⟨((x : ℚ).den : ℚ), hdenZp⟩ : ↥(Zp p)) = ⟨((x : ℚ).num : ℚ), hnumZp⟩ := by
      apply Subtype.ext
      show (x : ℚ) * ((x : ℚ).den : ℚ) = ((x : ℚ).num : ℚ)
      exact Rat.mul_den_eq_num (x : ℚ)
    have h2 := congrArg (red p A hmem) h1
    rw [map_mul] at h2
    have e1 : red p A hmem ⟨((x : ℚ).den : ℚ), hdenZp⟩ = ((x : ℚ).den : ResidueField ↥A) := by
      rw [show (⟨((x : ℚ).den : ℚ), hdenZp⟩ : ↥(Zp p)) = ((x : ℚ).den : ↥(Zp p)) from Subtype.ext (by simp),
        map_natCast]
    have e2 : red p A hmem ⟨((x : ℚ).num : ℚ), hnumZp⟩ = ((x : ℚ).num : ResidueField ↥A) := by
      rw [show (⟨((x : ℚ).num : ℚ), hnumZp⟩ : ↥(Zp p)) = ((x : ℚ).num : ↥(Zp p)) from Subtype.ext (by simp),
        map_intCast]
    rw [e1, e2] at h2
    exact h2
  have hdenz : (((x : ℚ).den : ZMod p)) ≠ 0 := by
    intro h; exact hden ((CharP.cast_eq_zero_iff (ZMod p) p _).mp h)
  rw [hzk, hz, map_mul, map_inv₀, map_intCast, map_natCast]
  rw [eq_mul_inv_iff_mul_eq₀ hdenk]
  exact hkey

theorem linearIndependent_red_of_saturated [CharP (ResidueField ↥A) p] {ι : Type*} [Fintype ι] {μ : Type*} (s : ι → μ → ↥(Zp p))
    (hsat : ∀ d : ι → ℤ, (∀ m, ∃ y : ↥(Zp p), ∑ i, ((d i : ℤ) : ↥(Zp p)) * s i m = (p : ↥(Zp p)) * y) →
      ∀ i, (p : ℤ) ∣ d i) :
    LinearIndependent (ResidueField ↥A) (fun i m => red p A hmem (s i m)) := by
  classical
  refine linearIndependent_of_natRel p _ (fun i m => exists_natCast_eq_red p A hmem (s i m)) ?_
  intro n hn i

  have hdiv : ∀ m, ∃ y : ↥(Zp p), ∑ j, ((n j : ℤ) : ↥(Zp p)) * s j m = (p : ↥(Zp p)) * y := by
    intro m
    apply exists_eq_p_mul_of_red_eq_zero p A hmem
    rw [map_sum]
    have : ∀ j, red p A hmem (((n j : ℤ) : ↥(Zp p)) * s j m) = (n j : ResidueField ↥A) * red p A hmem (s j m) := by
      intro j; rw [map_mul, map_intCast]; push_cast; rfl
    simp only [this]
    exact hn m
  have := hsat (fun j => (n j : ℤ)) hdiv i
  exact_mod_cast this

end Rational

end P2MZ5
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.P2MZ5"

namespace P2MZ5

section Orth
variable (p : ℕ) [Fact p.Prime]

theorem padicValRat_inv_pow (n : ℕ) : padicValRat p (((p : ℚ) ^ n)⁻¹) = -(n : ℤ) := by
  rw [padicValRat.inv, padicValRat.pow _,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → LaurentSeries ℚ) (n : ι → ℕ)
  (horth : ∀ c : ι → ℚ, (∀ m : ℤ, 0 ≤ padicValRat p ((∑ i, c i • F i).coeff m)) ↔
    ∀ i, -((n i : ℕ) : ℤ) ≤ padicValRat p (c i))

def resc (i : ι) (m : ℤ) : ℚ := ((p : ℚ) ^ (n i))⁻¹ * (F i).coeff m

include horth in

theorem resc_mem_Zp (i : ι) (m : ℤ) : resc p F n i m ∈ Zp p := by
  rw [mem_Zp_iff]
  have h := (horth (Pi.single i (((p : ℚ) ^ (n i))⁻¹))).mpr ?_ m
  · have e : (∑ j, (Pi.single i (((p : ℚ) ^ (n i))⁻¹) : ι → ℚ) j • F j).coeff m = resc p F n i m := by
      rw [HahnSeries.coeff_sum]
      simp only [HahnSeries.coeff_smul, Pi.single_apply, smul_eq_mul, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    rw [e] at h; exact h
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same, padicValRat_inv_pow]
    · rw [Pi.single_eq_of_ne hj, padicValRat.zero]; omega

include horth in

theorem resc_saturated (d : ι → ℤ)
    (hd : ∀ m, ∃ y : ℚ, y ∈ Zp p ∧ ∑ i, (d i : ℚ) * resc p F n i m = p * y) : ∀ i, (p : ℤ) ∣ d i := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  set c : ι → ℚ := fun i => (d i : ℚ) * ((p : ℚ) ^ (n i))⁻¹ / p with hc
  have hint : ∀ m : ℤ, 0 ≤ padicValRat p ((∑ i, c i • F i).coeff m) := by
    intro m
    obtain ⟨y, hy, hsum⟩ := hd m
    have e : (∑ i, c i • F i).coeff m = y := by
      rw [HahnSeries.coeff_sum]
      simp only [HahnSeries.coeff_smul, smul_eq_mul, hc]
      have : ∑ i, (d i : ℚ) * ((p : ℚ) ^ (n i))⁻¹ / p * (F i).coeff m
          = (∑ i, (d i : ℚ) * resc p F n i m) / p := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [resc]; ring
      rw [this, hsum]; field_simp
    rw [e]; exact (mem_Zp_iff p y).mp hy
  have hall := (horth c).mp hint
  intro i
  by_cases hdi : d i = 0
  · rw [hdi]; exact dvd_zero _
  · have h := hall i
    have hci : padicValRat p (c i) = padicValRat p (d i : ℚ) - (n i : ℤ) - 1 := by
      simp only [hc]
      rw [padicValRat.div (mul_ne_zero (by exact_mod_cast hdi) (inv_ne_zero (pow_ne_zero _ hp0))) hp0,
        padicValRat.mul (by exact_mod_cast hdi) (inv_ne_zero (pow_ne_zero _ hp0)), padicValRat_inv_pow,
        padicValRat.self (Fact.out : p.Prime).one_lt]
      ring
    rw [hci, padicValRat.of_int] at h
    have h1 : 1 ≤ padicValInt p (d i) := by omega
    have := (padicValInt_dvd_iff 1 (d i)).mpr (Or.inr h1)
    simpa using this

end Orth
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.P2MZ5"

end P2MZ5
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.P2MZ5"

open P2MZ5 in

theorem P2MZ5.linearIndependent_residue_resc_of_orth
    (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
    [CharP (IsLocalRing.ResidueField ↥A) p]
    (hmem : ∀ x : ℚ, x ∈ (Rat.padicValuation p).valuationSubring → algebraMap ℚ K x ∈ A)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → LaurentSeries ℚ) (n : ι → ℕ)
    (horth : ∀ c : ι → ℚ, (∀ m : ℤ, 0 ≤ padicValRat p ((∑ i, c i • F i).coeff m)) ↔
      ∀ i, -((n i : ℕ) : ℤ) ≤ padicValRat p (c i)) :
    LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun i (m : ℤ) => IsLocalRing.residue ↥A
        ⟨algebraMap ℚ K (((p : ℚ) ^ (n i))⁻¹ * (F i).coeff m), hmem _ (resc_mem_Zp p F n horth i m)⟩) := by
  have h := linearIndependent_red_of_saturated p A hmem
    (fun i m => (⟨resc p F n i m, resc_mem_Zp p F n horth i m⟩ : ↥(Zp p))) ?_
  · exact h
  · intro d hd
    apply resc_saturated p F n horth d
    intro m
    obtain ⟨y, hy⟩ := hd m
    refine ⟨(y : ℚ), y.2, ?_⟩
    have := congrArg (fun z : ↥(Zp p) => (z : ℚ)) hy
    simpa using this

namespace P2MZ5K

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering P2MZ5

theorem algebraMap_LS_eq_C {k : Type*} [Field k] (c : k) : algebraMap k (LaurentSeries k) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply']
  rw [show algebraMap k (PowerSeries k) c = PowerSeries.C c from by simp [PowerSeries.C_eq_algebraMap]]
  exact HahnSeries.ofPowerSeries_C c

theorem smul_bridge {k : Type*} [Field k] (c : k) (x : LaurentSeries k) :
    @HSMul.hSMul k _ _ (@instHSMul _ _ Algebra.toSMul) c x = @HSMul.hSMul k _ _ (@instHSMul _ _ HahnSeries.instSMul) c x := by
  rw [Algebra.smul_def, algebraMap_LS_eq_C, HahnSeries.C_mul_eq_smul]

variable {p : ℕ} [Fact p.Prime]

theorem coeff_frickeInvolutionBar_goodFamilyZero {r : ℕ} (D : FamData p r) (l : Fin r) (m : ℤ) :
    ((frickeInvolutionBar (1 * p) (goodFamilyZero D l) : ↥(modularFunctionFieldBar (1 * p))) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff m
      = algebraMap ℚ (AlgebraicClosure ℚ) ((((p : ℚ) ^ hasseExp D l)⁻¹) * (zeroSeries D l).coeff m) := by
  rw [goodFamilyZero, map_mul, map_inv₀, AlgEquiv.commutes]
  have e1 : ((((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹ * frickeInvolutionBar (1 * p) (D.t l) :
          ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)))
      = (HahnSeries.C ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹
          * ((frickeInvolutionBar (1 * p) (D.t l) : ↥(modularFunctionFieldBar (1 * p))) :
              LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, ← algebraMap_LS_eq_C]; rfl
  rw [e1, ← map_inv₀, coe_frickeInvolutionBar_t, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    coeffEmb_coeff]
  simp only [map_mul, map_inv₀, map_pow, map_natCast]

noncomputable def coeffLin (k : Type) [Field k] : ↥(modularFunctionFieldC k 1) →ₗ[k] (ℤ → k) where
  toFun x m := (x : LaurentSeries k).coeff m
  map_add' x y := by funext m; simp [HahnSeries.coeff_add]
  map_smul' c x := by
    funext m
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_LS_eq_C]
    simp

end P2MZ5K
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.P2MZ5"

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering P2MZ5 P2MZ5K in

theorem P2MZ5K.z5_main
    (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by
  classical

  have horth : ∀ c : Fin r → ℚ, (∀ m : ℤ, 0 ≤ padicValRat p ((∑ i, c i • zeroSeries D i).coeff m)) ↔
      ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i) := by
    intro c
    have e : ((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) :
        LaurentSeries ℚ) = ∑ i, c i • zeroSeries D i := by
      rw [IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_

      rw [Algebra.smul_def, IntermediateField.coe_mul, eq_ratCast (algebraMap ℚ ↥(modularFunctionFieldFull (1 * p))) (c i),
        SubfieldClass.coe_ratCast, ← eq_ratCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) (c i), HahnSeries.C_mul_eq_smul]
      rfl
    rw [← e]
    exact horthZero c

  have hmem : ∀ x : ℚ, x ∈ (Rat.padicValuation p).valuationSubring →
      algebraMap ℚ (AlgebraicClosure ℚ) x ∈ A :=
    fun x hx => (ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime A hA x).mpr hx

  have hLI := P2MZ5.linearIndependent_residue_resc_of_orth p A hmem (zeroSeries D) (hasseExp D) horth

  refine LinearIndependent.of_comp (coeffLin (IsLocalRing.ResidueField ↥A)) ?_
  convert hLI using 1
  funext l m

  have hf : ∀ n : ℤ, ((frickeInvolutionBar (1 * p) (goodFamilyZero D l) : ↥(modularFunctionFieldBar (1 * p))) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := by
    intro n
    rw [coeff_frickeInvolutionBar_goodFamilyZero]
    exact hmem _ (resc_mem_Zp p (zeroSeries D) (hasseExp D) horth l n)
  obtain ⟨h', hcoeff⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_of_forall_coeff_mem
      Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply (frickeInvolutionBar (1 * p) (goodFamilyZero D l)) hf
  show (((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ : ↥(modularFunctionFieldC _ 1)) :
      LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff m = _
  have hres : (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩
      = (ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply).residue
          ⟨frickeInvolutionBar (1 * p) (goodFamilyZero D l), h'⟩ := rfl
  rw [hres, hcoeff m]
  congr 1
  apply Subtype.ext
  exact coeff_frickeInvolutionBar_goodFamilyZero D l m

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering in

theorem solution
    (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) :=
  P2MZ5K.z5_main p D horthZero A hA Γ hint

end S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero
end P2MW
export P2MW.S_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero (solution)
