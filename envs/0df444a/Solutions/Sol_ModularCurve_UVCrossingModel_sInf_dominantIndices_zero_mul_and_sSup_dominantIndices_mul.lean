-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0fb8e2cd-60cf-5802-9960-b49b22235150

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_mul_scale
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
import Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_scale
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_succ_sub_eq_sInf_dominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

namespace EndSlopeSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

variable {W : Type u} [CommRing W]

@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, nfExponent_natCast, nfCoeff_natCast, coeff_inU_add_inV]
    simp only [Finsupp.single_apply, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [nfExponent_negSucc, nfCoeff_negSucc, coeff_inU_add_inV]
    simp [Finsupp.single_apply]

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem termOrder_negSucc (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    termOrder v E t ab (Int.negSucc j) = v (PowerSeries.coeff (j + 1) ab.2) + (((j + 1) * (E - t) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem iInf_termOrder_lt_top (v : W → ℕ∞) (hv : ∀ c, v c = ⊤ → c = 0) (π : W) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : (⨅ n : ℤ, termOrder v E t ab n) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hx
  have hall : ∀ n, termOrder v E t ab n = ⊤ := fun n => top_le_iff.mp (htop ▸ iInf_le _ n)
  have hcoef : ∀ n, nfCoeff ab n = 0 := fun n => by
    apply hv
    have := hall n
    rw [termOrder] at this
    exact (WithTop.add_eq_top.mp this).resolve_right (ENat.coe_ne_top _)
  have ha : ab.1 = 0 := by
    ext i; simpa using hcoef (i : ℤ)
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hcoef (Int.negSucc j)
  have h0 : inU ab.1 + inV ab.2 = 0 := by
    ext d; rw [coeff_inU_add_inV, ha, hb']; simp
  rw [h0, map_zero]

section Scaled
variable [IsDomain W] [IsDiscreteValuationRing W]

noncomputable abbrev vq (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) : W → ℕ∞ :=
  fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w

theorem vq_zero (q : ℕ) (hq : 1 ≤ q) : vq W q 0 = ⊤ := by
  simp only [vq, AddValuation.map_zero]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr (by omega))

theorem vq_eq_top (q : ℕ) (c : W) (h : vq W q c = ⊤) : c = 0 := by
  simp only [vq] at h
  rcases WithTop.mul_eq_top_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact IsDiscreteValuationRing.addVal_eq_top_iff.mp h2
  · exact absurd h1 (ENat.coe_ne_top q)

end Scaled

end EndSlopeSol
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul.EndSlopeSol"

namespace EndSlopeMain

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem exists_addVal_nfCoeff_ne_top (ϖ : W) (e : ℕ)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    ∃ n : ℤ, IsDiscreteValuationRing.addVal W (nfCoeff ab n) ≠ ⊤ := by
  have h := EndSlopeSol.iInf_termOrder_lt_top (IsDiscreteValuationRing.addVal W : W → ℕ∞)
    (fun c hc => IsDiscreteValuationRing.addVal_eq_top_iff.mp hc) (ϖ ^ e) e 0 ab hb (habx ▸ hx)
  by_contra hall
  push Not at hall
  apply h.ne
  rw [iInf_eq_top]
  intro n
  rw [termOrder, hall n, top_add]

theorem solution_core
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    [IsDomain (UVCrossingModel W (ϖ ^ e))]
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'') =
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) +
          sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab') ∧
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'') =
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) +
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab') := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  set v := IsDiscreteValuationRing.addVal W
  have hv0 : (v : W → ℕ∞) 0 = ⊤ := AddValuation.map_zero v

  obtain ⟨N₁, K₁⟩ := exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ (v : W → ℕ∞) hv0 e he ab hb (exists_addVal_nfCoeff_ne_top ϖ e x hx ab hb habx)
  obtain ⟨N₂, K₂⟩ := exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ (v : W → ℕ∞) hv0 e he ab' hb' (exists_addVal_nfCoeff_ne_top ϖ e y hy ab' hb' haby)
  obtain ⟨N₃, K₃⟩ := exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ (v : W → ℕ∞) hv0 e he ab'' hb'' (exists_addVal_nfCoeff_ne_top ϖ e (x * y) hxy ab'' hb'' habxy)
  set N := N₁ + N₂ + N₃ with hN
  set q := Nat.factorial N with hqdef
  have hq : 1 ≤ q := Nat.factorial_pos N
  have d1 : Nat.factorial N₁ ∣ q := Nat.factorial_dvd_factorial (by omega)
  have d2 : Nat.factorial N₂ ∣ q := Nat.factorial_dvd_factorial (by omega)
  have d3 : Nat.factorial N₃ ∣ q := Nat.factorial_dvd_factorial (by omega)
  obtain ⟨K₁b, K₁t⟩ := K₁ q hq d1
  obtain ⟨K₂b, K₂t⟩ := K₂ q hq d2
  obtain ⟨K₃b, K₃t⟩ := K₃ q hq d3
  have hqe : 0 + 1 ≤ q * e := by nlinarith

  have Dx := gaussOrder_succ_sub_eq_sInf_dominantIndices ϖ hϖ e he q hq x hx ab hb habx 0 hqe (K₁b 0 hqe)
  have Dy := gaussOrder_succ_sub_eq_sInf_dominantIndices ϖ hϖ e he q hq y hy ab' hb' haby 0 hqe (K₂b 0 hqe)
  have Dxy := gaussOrder_succ_sub_eq_sInf_dominantIndices ϖ hϖ e he q hq (x * y) hxy ab'' hb'' habxy 0 hqe (K₃b 0 hqe)
  have G0 := gaussOrder_mul_scale ϖ hϖ e he q hq x y 0 (by omega)
  have G1 := gaussOrder_mul_scale ϖ hϖ e he q hq x y (0 + 1) hqe

  have S0 : ∀ ab₀ : PowerSeries W × PowerSeries W,
      dominantIndices (fun w => (q : ℕ∞) * v w) (q * e) 0 ab₀ = dominantIndices v e 0 ab₀ := fun ab₀ => by
    simpa using dominantIndices_scale (v : W → ℕ∞) e 0 q hq ab₀
  have Se : ∀ ab₀ : PowerSeries W × PowerSeries W,
      dominantIndices (fun w => (q : ℕ∞) * v w) (q * e) (q * e) ab₀ = dominantIndices v e e ab₀ := fun ab₀ =>
    dominantIndices_scale (v : W → ℕ∞) e e q hq ab₀

  have hqe' : q * e ≤ q * e := le_rfl
  have h1qe : 1 ≤ q * e := by omega
  have Ux := gaussOrder_sub_pred_eq_sSup_dominantIndices ϖ hϖ e he q hq x hx ab hb habx (q * e) h1qe hqe' (K₁t (q * e) h1qe le_rfl)
  have Uy := gaussOrder_sub_pred_eq_sSup_dominantIndices ϖ hϖ e he q hq y hy ab' hb' haby (q * e) h1qe hqe' (K₂t (q * e) h1qe le_rfl)
  have Uxy := gaussOrder_sub_pred_eq_sSup_dominantIndices ϖ hϖ e he q hq (x * y) hxy ab'' hb'' habxy (q * e) h1qe hqe' (K₃t (q * e) h1qe le_rfl)
  have Ge := gaussOrder_mul_scale ϖ hϖ e he q hq x y (q * e) le_rfl
  have Ge1 := gaussOrder_mul_scale ϖ hϖ e he q hq x y (q * e - 1) (by omega)

  have fin : ∀ (z : UVCrossingModel W (ϖ ^ e)) (abz : PowerSeries W × PowerSeries W),
      PowerSeries.constantCoeff abz.2 = 0 → mk (ϖ ^ e) (inU abz.1 + inV abz.2) = z → z ≠ 0 → ∀ p, p ≤ q * e →
      gaussOrder (fun w => (q : ℕ∞) * v w) (ϖ ^ e) (q * e) p z < ⊤ := by
    intro z abz hbz habz hz p hp
    rw [gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he q hq z abz hbz habz p hp,
      repGaussOrder_normalForm_eq_iInf_termOrder _ (EndSlopeSol.vq_zero (W := W) q hq) (q * e) p abz hbz]
    exact EndSlopeSol.iInf_termOrder_lt_top (EndSlopeSol.vq W q) (EndSlopeSol.vq_eq_top q) (ϖ ^ e) (q * e) p abz hbz (habz ▸ hz)

  have tonat_add : ∀ {A B C : ℕ∞}, A < ⊤ → B < ⊤ → C = A + B → (C.toNat : ℤ) = A.toNat + B.toNat := by
    intro A B C hA hB hC
    obtain ⟨a, rfl⟩ := ENat.ne_top_iff_exists.mp hA.ne
    obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB.ne
    subst hC
    have hab : ((a : ℕ∞) + (b : ℕ∞)) = ((a + b : ℕ) : ℕ∞) := (Nat.cast_add a b).symm
    rw [hab, ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe, Nat.cast_add]
  have fx := fin x ab hb habx hx
  have fy := fin y ab' hb' haby hy
  constructor
  ·
    have e0 := tonat_add (fx 0 (by omega)) (fy 0 (by omega)) G0
    have e1 := tonat_add (fx (0 + 1) hqe) (fy (0 + 1) hqe) G1
    rw [← S0 ab'', ← S0 ab, ← S0 ab', ← Dxy, ← Dx, ← Dy, e0, e1]
    ring
  ·
    have e0 := tonat_add (fx (q * e) le_rfl) (fy (q * e) le_rfl) Ge
    have e1 := tonat_add (fx (q * e - 1) (by omega)) (fy (q * e - 1) (by omega)) Ge1
    rw [← Se ab'', ← Se ab, ← Se ab', ← Uxy, ← Ux, ← Uy, e0, e1]
    ring

end EndSlopeMain
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul.EndSlopeSol"

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'') =
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) +
          sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab') ∧
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'') =
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) +
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab') := by
  haveI : IsDomain (UVCrossingModel W (ϖ ^ e)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he).1
  exact EndSlopeMain.solution_core ϖ hϖ e he x hx ab hb habx y hy ab' hb' haby ab'' hb'' habxy

end S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul (solution)
