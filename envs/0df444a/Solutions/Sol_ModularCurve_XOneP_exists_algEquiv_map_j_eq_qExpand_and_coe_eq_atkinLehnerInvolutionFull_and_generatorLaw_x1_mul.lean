-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e2d8c2a8-57ec-5adc-a88a-377d1e1eadcb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane HahnSeries ModularCurve~coeffEmb_qExpand~coeffMap_injective"
open scoped MatrixGroups ModularForm

namespace INVOL

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev MF (N : ℕ) (k : ℤ) := ModularForm (Γ1 N) k

variable {N : ℕ}

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by
  simp [Γ1]

def Q {k : ℤ} (f : MF N k) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f)

theorem Q_mul {a b : ℤ} (f : MF N a) (g : MF N b) : Q (f.mul g) = Q f * Q g := by
  rw [Q, Q, Q, ← map_mul, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

theorem Q_add {k : ℤ} (f g : MF N k) : Q (f + g) = Q f + Q g := by
  rw [Q, Q, Q, ← map_add, ModularForm.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem Q_smul {k : ℤ} (c : ℂ) (f : MF N k) : Q (c • f) = HahnSeries.C c * Q f := by
  rw [Q, Q, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c,
    PowerSeries.smul_eq_C_mul, map_mul, ofPowerSeries_C]

theorem Q_sub {k : ℤ} (f g : MF N k) : Q (f - g) = Q f - Q g := by
  rw [Q, Q, Q, ← map_sub, ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods f g]

theorem Q_zero {k : ℤ} : Q (0 : MF N k) = 0 := by
  rw [Q, ModularForm.coe_zero, qExpansion_zero, map_zero]

theorem Q_eq_zero_iff {k : ℤ} (f : MF N k) : Q f = 0 ↔ f = 0 := by
  rw [Q, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact ⟨fun h => ofPowerSeries_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

theorem Q_injective {k : ℤ} : Function.Injective (Q (N := N) (k := k)) := by
  intro f g h
  have : Q (f - g) = 0 := by rw [Q_sub, h, sub_self]
  exact sub_eq_zero.mp ((Q_eq_zero_iff _).mp this)

theorem Q_sum {k : ℤ} {ι : Type} (s : Finset ι) (f : ι → MF N k) : Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Q_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Q_add, ih]

theorem Q_eq_intSeriesC {k : ℤ} {f : MF N k} {r : PowerSeries ℤ} (h : IsIntegralQExp f r) :
    Q f = intSeriesC ℂ r := by
  rw [Q, intSeriesC, ← h]

section LForms

variable (Lc : Subfield ℂ)

scoped instance instModuleSubfield {k : ℤ} : Module Lc (MF N k) :=
  Function.Injective.module Lc (FunLike.coeAddMonoidHom (MF N k) UpperHalfPlane ℂ) DFunLike.coe_injective
    (fun _ _ => rfl)

theorem subfield_smul_eq {k : ℤ} (c : Lc) (f : MF N k) : c • f = (c : ℂ) • f := rfl

def intForms (N : ℕ) (k : ℤ) : Set (MF N k) := {F | ∃ r : PowerSeries ℤ, IsIntegralQExp F r}

def LForms (k : ℤ) : Submodule Lc (MF N k) := Submodule.span Lc (intForms N k)

variable {Lc}

theorem mem_LForms_of_isIntegral {k : ℤ} {F : MF N k} {r : PowerSeries ℤ} (h : IsIntegralQExp F r) :
    F ∈ LForms Lc k := Submodule.subset_span ⟨r, h⟩

theorem sum_smul_mem_LForms {k : ℤ} {n : ℕ} (c : Fin n → ℂ) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ)
    (hc : ∀ i, c i ∈ Lc) (hF : ∀ i, IsIntegralQExp (F i) (r i)) :
    (∑ i, c i • F i) ∈ LForms Lc k := by
  refine Submodule.sum_mem _ fun i _ => ?_
  have : c i • F i = (⟨c i, hc i⟩ : Lc) • F i := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (mem_LForms_of_isIntegral (hF i))

theorem isIntegralQExp_mul {a b : ℤ} {f : MF N a} {g : MF N b} {r s : PowerSeries ℤ}
    (hf : IsIntegralQExp f r) (hg : IsIntegralQExp g s) : IsIntegralQExp (f.mul g) (r * s) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul,
    ← ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g]

theorem mul_mem_LForms {a b : ℤ} {f : MF N a} {g : MF N b} (hf : f ∈ LForms Lc a) (hg : g ∈ LForms Lc b) :
    f.mul g ∈ LForms Lc (a + b) := by
  induction hf using Submodule.span_induction generalizing g with
  | mem F hF =>
    obtain ⟨r, hr⟩ := hF
    induction hg using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨s', hs⟩ := hG
      exact mem_LForms_of_isIntegral (isIntegralQExp_mul hr hs)
    | zero =>
      have : F.mul (0 : MF N b) = 0 := by ext τ; simp [ModularForm.coe_mul]
      rw [this]; exact Submodule.zero_mem _
    | add G G' _ _ h1 h2 =>
      have : F.mul (G + G') = F.mul G + F.mul G' := by ext τ; simp [ModularForm.coe_mul, mul_add]
      rw [this]; exact Submodule.add_mem _ h1 h2
    | smul c G _ h1 =>
      have : F.mul (c • G) = c • F.mul G := by
        ext τ; simp [ModularForm.coe_mul, subfield_smul_eq, mul_left_comm]
      rw [this]; exact Submodule.smul_mem _ _ h1
  | zero =>
    have : (0 : MF N a).mul g = 0 := by ext τ; simp [ModularForm.coe_mul]
    rw [this]; exact Submodule.zero_mem _
  | add F F' _ _ h1 h2 =>
    have : (F + F').mul g = F.mul g + F'.mul g := by ext τ; simp [ModularForm.coe_mul, add_mul]
    rw [this]; exact Submodule.add_mem _ (h1 hg) (h2 hg)
  | smul c F _ h1 =>
    have : (c • F).mul g = c • F.mul g := by
      ext τ; simp [ModularForm.coe_mul, subfield_smul_eq, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ _ (h1 hg)

theorem exists_Q_eq_sum_of_mem_LForms {k : ℤ} {f : MF N k} (hf : f ∈ LForms Lc k) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ Lc) ∧ (∀ i, IsIntegralQExp (F i) (r i)) ∧ f = ∑ i, c i • F i := by
  induction hf using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨r, hr⟩ := hF
    exact ⟨1, fun _ => 1, fun _ => F, fun _ => r, fun _ => Lc.one_mem, fun _ => hr, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add F F' _ _ h1 h2 =>
    obtain ⟨n, c, G, r, hc, hG, rfl⟩ := h1
    obtain ⟨n', c', G', r', hc', hG', rfl⟩ := h2
    refine ⟨n + n', Fin.append c c', Fin.append G G', Fin.append r r', fun i => ?_, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hc, hc']
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hG, hG']
    · rw [Fin.sum_univ_add]; simp
  | smul a F _ h1 =>
    obtain ⟨n, c, G, r, hc, hG, rfl⟩ := h1
    refine ⟨n, fun i => (a : ℂ) * c i, G, r, fun i => Lc.mul_mem a.2 (hc i), hG, ?_⟩
    rw [subfield_smul_eq, Finset.smul_sum]
    simp [mul_smul]

end LForms

section WOp

variable (p : ℕ) (γ : SL(2, ℤ))

def Wfun (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ => (f ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)

variable {p γ}

theorem Wfun_add (k : ℤ) (f g : ℍ → ℂ) : Wfun p γ k (f + g) = Wfun p γ k f + Wfun p γ k g := by
  ext τ; simp [Wfun, SlashAction.add_slash]

theorem Wfun_zero (k : ℤ) : Wfun p γ k (0 : ℍ → ℂ) = 0 := by
  ext τ; simp [Wfun, SlashAction.zero_slash]

theorem Wfun_smul (k : ℤ) (c : ℂ) (f : ℍ → ℂ) : Wfun p γ k (c • f) = c • Wfun p γ k f := by
  ext τ; simp [Wfun, ModularForm.SL_smul_slash]

theorem Wfun_mul (a b : ℤ) (f g : ℍ → ℂ) : Wfun p γ (a + b) (f * g) = Wfun p γ a f * Wfun p γ b g := by
  ext τ; simp [Wfun, ModularForm.mul_slash_SL2]

theorem Wfun_sum (k : ℤ) {ι : Type} (s : Finset ι) (f : ι → ℍ → ℂ) :
    Wfun p γ k (∑ i ∈ s, f i) = ∑ i ∈ s, Wfun p γ k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Wfun_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Wfun_add, ih]

variable (N p γ) (Lc : Subfield ℂ) in

def WPHyp : Prop :=
  ∀ (k : ℤ) (f : MF N k) (p₀ : PowerSeries ℤ), IsIntegralQExp f p₀ →
    ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ),
      D ≠ 0 ∧ (∀ i, c i ∈ Lc) ∧ (∀ i, IsIntegralQExp (F i) (r i)) ∧
      ((D : ℂ) • Wfun p γ k (⇑f : ℍ → ℂ)) = ∑ i, c i • (⇑(F i) : ℍ → ℂ)

theorem coe_finset_sum {k : ℤ} {ι : Type} (s : Finset ι) (F : ι → MF N k) :
    (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm (Γ1 N) k) UpperHalfPlane ℂ) F s

variable {Lc : Subfield ℂ}

theorem exists_mem_LForms_coe_eq_smul_Wfun (hW : WPHyp N p γ Lc) {k : ℤ} {f : MF N k} (hf : f ∈ LForms Lc k) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ g : MF N k, g ∈ LForms Lc k ∧ (⇑g : ℍ → ℂ) = (D : ℂ) • Wfun p γ k ⇑f := by
  induction hf using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨r, hr⟩ := hF
    obtain ⟨D, n, c, G, s, hD, hc, hG, heq⟩ := hW k F r hr
    refine ⟨D, hD, ∑ i, c i • G i, sum_smul_mem_LForms c G s hc hG, ?_⟩
    rw [coe_finset_sum, heq]
    simp
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp [Wfun_zero]⟩
  | add F F' _ _ h1 h2 =>
    obtain ⟨D₁, hD₁, g₁, hg₁, e₁⟩ := h1
    obtain ⟨D₂, hD₂, g₂, hg₂, e₂⟩ := h2
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, ((D₂ : ℤ) : Lc) • g₁ + ((D₁ : ℤ) : Lc) • g₂,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hg₁) (Submodule.smul_mem _ _ hg₂), ?_⟩
    rw [ModularForm.coe_add, subfield_smul_eq, subfield_smul_eq, ModularForm.IsGLPos.coe_smul,
      ModularForm.IsGLPos.coe_smul, e₁, e₂, ModularForm.coe_add, Wfun_add, smul_add, smul_smul, smul_smul]
    push_cast
    congr 1
    rw [mul_comm]
  | smul a F _ h1 =>
    obtain ⟨D, hD, g, hg, e⟩ := h1
    refine ⟨D, hD, a • g, Submodule.smul_mem _ _ hg, ?_⟩
    rw [subfield_smul_eq, subfield_smul_eq, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, e,
      Wfun_smul, smul_comm]

end WOp

section Ratio

variable {p : ℕ} {γ : SL(2, ℤ)} {Lc : Subfield ℂ}

theorem Wfun_eq_zero_iff [NeZero p] (k : ℤ) (h : ℍ → ℂ) : Wfun p γ k h = 0 ↔ h = 0 := by
  constructor
  · intro H
    have H1 : h ∣[k] γ = 0 := by
      ext τ
      have := congrFun H ((ModularForm.heckeDiagMatrix p)⁻¹ • τ)
      simpa [Wfun, smul_smul] using this
    have : h = (h ∣[k] γ) ∣[k] γ⁻¹ := by rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [this, H1, SlashAction.zero_slash]
  · rintro rfl; exact Wfun_zero k

structure WData (p : ℕ) (γ : SL(2, ℤ)) (Lc : Subfield ℂ) {k : ℤ} (f : MF N k) where
  D : ℤ
  hD : D ≠ 0
  φ : MF N k
  hφ : φ ∈ LForms Lc k
  eq : (⇑φ : ℍ → ℂ) = (D : ℂ) • Wfun p γ k ⇑f

def wdata (hW : WPHyp N p γ Lc) {k : ℤ} {f : MF N k} (hf : f ∈ LForms Lc k) : WData p γ Lc f :=
  let h := exists_mem_LForms_coe_eq_smul_Wfun hW hf
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose, h.choose_spec.2.choose_spec.1, h.choose_spec.2.choose_spec.2⟩

theorem WData.Q_ne_zero [NeZero p] {k : ℤ} {g : MF N k} (e : WData p γ Lc g) (hg : Q g ≠ 0) : Q e.φ ≠ 0 := by
  intro h0
  have hφ : e.φ = 0 := (Q_eq_zero_iff _).mp h0
  have : (e.D : ℂ) • Wfun p γ k ⇑g = 0 := by rw [← e.eq, hφ, ModularForm.coe_zero]
  rw [smul_eq_zero, Int.cast_eq_zero] at this
  rcases this with h | h
  · exact e.hD h
  · rw [Wfun_eq_zero_iff] at h
    exact hg ((Q_eq_zero_iff g).mpr (DFunLike.coe_injective (h.trans ModularForm.coe_zero.symm)))

def wval {k : ℤ} {f g : MF N k} (d : WData p γ Lc f) (e : WData p γ Lc g) : LaurentSeries ℂ :=
  HahnSeries.C ((e.D : ℂ) / d.D) * Q d.φ / Q e.φ

def WData.mul {a b : ℤ} {f : MF N a} {g : MF N b} (d : WData p γ Lc f) (e : WData p γ Lc g) :
    WData p γ Lc (f.mul g) where
  D := d.D * e.D
  hD := mul_ne_zero d.hD e.hD
  φ := d.φ.mul e.φ
  hφ := mul_mem_LForms d.hφ e.hφ
  eq := by
    rw [ModularForm.coe_mul, d.eq, e.eq, ModularForm.coe_mul, Wfun_mul]
    ext τ; simp; ring

theorem coe_eq_of_Q_mul_eq {a b : ℤ} {f : MF N a} {g' : MF N b} {f' : MF N b} {g : MF N a}
    (h : Q f * Q g' = Q f' * Q g) : (⇑f : ℍ → ℂ) * ⇑g' = ⇑f' * ⇑g := by
  have hm : Q ((f'.mul g).mcast (add_comm b a)) = Q (f'.mul g) := rfl
  have h1 : Q (f.mul g') = Q ((f'.mul g).mcast (add_comm b a)) := by
    rw [hm, Q_mul, Q_mul, h]
  have := Q_injective h1
  have := congrArg (fun F : MF N (a + b) => (⇑F : ℍ → ℂ)) this
  simpa [ModularForm.coe_mul] using this

theorem wval_eq_wval {a b : ℤ} {f g : MF N a} {f' g' : MF N b}
    (d : WData p γ Lc f) (e : WData p γ Lc g) (d' : WData p γ Lc f') (e' : WData p γ Lc g')
    (hg : Q e.φ ≠ 0) (hg' : Q e'.φ ≠ 0)
    (h : Q f * Q g' = Q f' * Q g) : wval d e = wval d' e' := by

  have hfun := coe_eq_of_Q_mul_eq h
  have hW : Wfun p γ a ⇑f * Wfun p γ b ⇑g' = Wfun p γ b ⇑f' * Wfun p γ a ⇑g := by
    rw [← Wfun_mul, ← Wfun_mul, hfun, add_comm]

  have hforms : ((d'.D : ℂ) * e.D) • ((⇑d.φ : ℍ → ℂ) * ⇑e'.φ) = ((d.D : ℂ) * e'.D) • ((⇑d'.φ : ℍ → ℂ) * ⇑e.φ) := by
    rw [d.eq, e.eq, d'.eq, e'.eq]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have := congrFun hW τ
    simp only [Pi.mul_apply] at this
    linear_combination ((d.D : ℂ) * e.D * d'.D * e'.D) * this
  have hQ : HahnSeries.C ((d'.D : ℂ) * e.D) * (Q d.φ * Q e'.φ) = HahnSeries.C ((d.D : ℂ) * e'.D) * (Q d'.φ * Q e.φ) := by
    have e1 : Q ((((d'.D : ℂ) * e.D) • d.φ).mul e'.φ) = Q (((((d.D : ℂ) * e'.D) • d'.φ).mul e.φ).mcast (add_comm b a)) := by
      congr 1
      apply DFunLike.coe_injective
      simp only [ModularForm.coe_mul, ModularForm.IsGLPos.coe_smul]
      rw [show (⇑((((d.D : ℂ) * e'.D) • d'.φ).mul e.φ |>.mcast (add_comm b a)) : ℍ → ℂ) =
        ((d.D : ℂ) * e'.D) • ⇑d'.φ * ⇑e.φ from rfl]
      rw [smul_mul_assoc, smul_mul_assoc]; exact hforms
    rw [Q_mul, Q_smul] at e1
    rw [show Q (((((d.D : ℂ) * e'.D) • d'.φ).mul e.φ).mcast (add_comm b a)) = Q ((((d.D : ℂ) * e'.D) • d'.φ).mul e.φ) from rfl,
      Q_mul, Q_smul] at e1
    rw [← mul_assoc, ← mul_assoc]; exact e1

  have hd : (d.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d.hD
  have hd' : (d'.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d'.hD
  have he : (e.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e.hD
  have he' : (e'.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e'.hD
  rw [wval, wval, div_eq_div_iff hg hg']
  have hC : ∀ u v : ℂ, (HahnSeries.C (u * v) : LaurentSeries ℂ) = HahnSeries.C u * HahnSeries.C v :=
    fun u v => map_mul _ u v
  have hCd : ∀ u v : ℂ, v ≠ 0 → (HahnSeries.C (u / v) : LaurentSeries ℂ) = HahnSeries.C u * (HahnSeries.C v)⁻¹ :=
    fun u v hv => by rw [div_eq_mul_inv, hC, map_inv₀]
  rw [hCd _ _ hd, hCd _ _ hd']
  have hCne : ∀ u : ℂ, u ≠ 0 → (HahnSeries.C u : LaurentSeries ℂ) ≠ 0 := fun u hu =>
    (map_ne_zero HahnSeries.C).mpr hu
  rw [hC, hC] at hQ
  apply mul_left_cancel₀ (mul_ne_zero (hCne _ hd) (hCne _ hd'))
  have l1 : HahnSeries.C (d.D : ℂ) * HahnSeries.C (d'.D : ℂ) *
      (HahnSeries.C (e.D : ℂ) * (HahnSeries.C (d.D : ℂ))⁻¹ * Q d.φ * Q e'.φ)
      = HahnSeries.C (d'.D : ℂ) * HahnSeries.C (e.D : ℂ) * (Q d.φ * Q e'.φ) *
        (HahnSeries.C (d.D : ℂ) * (HahnSeries.C (d.D : ℂ))⁻¹) := by ring
  have l2 : HahnSeries.C (d.D : ℂ) * HahnSeries.C (d'.D : ℂ) *
      (HahnSeries.C (e'.D : ℂ) * (HahnSeries.C (d'.D : ℂ))⁻¹ * Q d'.φ * Q e.φ)
      = HahnSeries.C (d.D : ℂ) * HahnSeries.C (e'.D : ℂ) * (Q d'.φ * Q e.φ) *
        (HahnSeries.C (d'.D : ℂ) * (HahnSeries.C (d'.D : ℂ))⁻¹) := by ring
  rw [l1, l2, mul_inv_cancel₀ (hCne _ hd), mul_inv_cancel₀ (hCne _ hd'), mul_one, mul_one, hQ]

end Ratio

section RatioField

variable (Lc : Subfield ℂ)

structure Rep (x : LaurentSeries ℂ) where
  k : ℤ
  f : MF N k
  g : MF N k
  hf : f ∈ LForms Lc k
  hg : g ∈ LForms Lc k
  hQg : Q g ≠ 0
  eq : x * Q g = Q f

variable {Lc}

theorem Rep.x_eq {x : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) : x = Q ρ.f / Q ρ.g := by
  rw [eq_div_iff ρ.hQg, ρ.eq]

theorem one_mem_LForms : (1 : MF N 0) ∈ LForms Lc 0 :=
  mem_LForms_of_isIntegral (r := 1) (by
    show IsIntegralQExp (⇑(1 : MF N 0)) 1
    rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one)

theorem Q_one : Q (1 : MF N 0) = 1 := by
  rw [Q, ModularForm.one_coe_eq_one, qExpansion_one, map_one]

def Rep.one : Rep (N := N) Lc 1 := ⟨0, 1, 1, one_mem_LForms, one_mem_LForms, by rw [Q_one]; exact one_ne_zero, by rw [Q_one, mul_one]⟩

def Rep.zero : Rep (N := N) Lc 0 := ⟨0, 0, 1, Submodule.zero_mem _, one_mem_LForms, by rw [Q_one]; exact one_ne_zero,
  by rw [Q_zero, zero_mul]⟩

def Rep.mul {x y : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) (ρ' : Rep (N := N) Lc y) : Rep (N := N) Lc (x * y) where
  k := ρ.k + ρ'.k
  f := ρ.f.mul ρ'.f
  g := ρ.g.mul ρ'.g
  hf := mul_mem_LForms ρ.hf ρ'.hf
  hg := mul_mem_LForms ρ.hg ρ'.hg
  hQg := by rw [Q_mul]; exact mul_ne_zero ρ.hQg ρ'.hQg
  eq := by rw [Q_mul, Q_mul, ← ρ.eq, ← ρ'.eq]; ring

theorem mcast_mem_LForms {a b : ℤ} (h : a = b) {f : MF N a} (hf : f ∈ LForms Lc a) : f.mcast h ∈ LForms Lc b := by
  subst h; exact hf

theorem Q_mcast {a b : ℤ} (h : a = b) (f : MF N a) : Q (f.mcast h) = Q f := rfl

def Rep.add {x y : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) (ρ' : Rep (N := N) Lc y) : Rep (N := N) Lc (x + y) where
  k := ρ.k + ρ'.k
  f := ρ.f.mul ρ'.g + (ρ'.f.mul ρ.g).mcast (add_comm _ _)
  g := ρ.g.mul ρ'.g
  hf := Submodule.add_mem _ (mul_mem_LForms ρ.hf ρ'.hg) (mcast_mem_LForms _ (mul_mem_LForms ρ'.hf ρ.hg))
  hg := mul_mem_LForms ρ.hg ρ'.hg
  hQg := by rw [Q_mul]; exact mul_ne_zero ρ.hQg ρ'.hQg
  eq := by rw [Q_add, Q_mcast, Q_mul, Q_mul, Q_mul, ← ρ.eq, ← ρ'.eq]; ring

def Rep.neg {x : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) : Rep (N := N) Lc (-x) where
  k := ρ.k
  f := -ρ.f
  g := ρ.g
  hf := Submodule.neg_mem _ ρ.hf
  hg := ρ.hg
  hQg := ρ.hQg
  eq := by
    have : Q (-ρ.f) = -Q ρ.f := by
      have h := Q_add ρ.f (-ρ.f); rw [add_neg_cancel, Q_zero] at h
      linear_combination -h
    rw [this, ← ρ.eq]; ring

def Rep.inv {x : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) (hx : x ≠ 0) : Rep (N := N) Lc x⁻¹ where
  k := ρ.k
  f := ρ.g
  g := ρ.f
  hf := ρ.hg
  hg := ρ.hf
  hQg := by intro h; rw [ρ.x_eq, h, zero_div] at hx; exact hx rfl
  eq := by
    rw [← ρ.eq, inv_mul_cancel_left₀ hx]

variable (N Lc) in

def ratioField : Subfield (LaurentSeries ℂ) where
  carrier := {x | Nonempty (Rep (N := N) Lc x)}
  mul_mem' := fun ⟨ρ⟩ ⟨ρ'⟩ => ⟨ρ.mul ρ'⟩
  one_mem' := ⟨Rep.one⟩
  add_mem' := fun ⟨ρ⟩ ⟨ρ'⟩ => ⟨ρ.add ρ'⟩
  zero_mem' := ⟨Rep.zero⟩
  neg_mem' := fun ⟨ρ⟩ => ⟨ρ.neg⟩
  inv_mem' := fun x ⟨ρ⟩ => by
    by_cases hx : x = 0
    · rw [hx, inv_zero]; exact ⟨Rep.zero⟩
    · exact ⟨ρ.inv hx⟩

theorem mem_ratioField_iff {x : LaurentSeries ℂ} : x ∈ ratioField N Lc ↔ Nonempty (Rep (N := N) Lc x) := Iff.rfl

theorem div_mem_ratioField {k : ℤ} {f g : MF N k} (hf : f ∈ LForms Lc k) (hg : g ∈ LForms Lc k) (hQg : Q g ≠ 0) :
    Q f / Q g ∈ ratioField N Lc := ⟨⟨k, f, g, hf, hg, hQg, div_mul_cancel₀ _ hQg⟩⟩

end RatioField

section Phi

variable {p : ℕ} [NeZero p] {γ : SL(2, ℤ)} {Lc : Subfield ℂ} (hW : WPHyp N p γ Lc)

def phiRep {x : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) : LaurentSeries ℂ :=
  wval (wdata hW ρ.hf) (wdata hW ρ.hg)

theorem phiRep_eq_wval {x : LaurentSeries ℂ} (ρ : Rep (N := N) Lc x) (d : WData p γ Lc ρ.f) (e : WData p γ Lc ρ.g) :
    phiRep hW ρ = wval d e :=
  wval_eq_wval _ _ _ _ ((wdata hW ρ.hg).Q_ne_zero ρ.hQg) (e.Q_ne_zero ρ.hQg) rfl

theorem phiRep_eq_phiRep {x : LaurentSeries ℂ} (ρ ρ' : Rep (N := N) Lc x) : phiRep hW ρ = phiRep hW ρ' := by
  apply wval_eq_wval _ _ _ _ ((wdata hW ρ.hg).Q_ne_zero ρ.hQg) ((wdata hW ρ'.hg).Q_ne_zero ρ'.hQg)
  rw [← ρ.eq, ← ρ'.eq]; ring

def phiFun (x : ratioField N Lc) : LaurentSeries ℂ := phiRep hW (Classical.choice x.2)

theorem phiFun_eq {x : LaurentSeries ℂ} (hx : x ∈ ratioField N Lc) (ρ : Rep (N := N) Lc x) :
    phiFun hW ⟨x, hx⟩ = phiRep hW ρ := phiRep_eq_phiRep hW _ _

theorem wval_mul {a b : ℤ} {f g : MF N a} {f' g' : MF N b}
    (d : WData p γ Lc f) (e : WData p γ Lc g) (d' : WData p γ Lc f') (e' : WData p γ Lc g') :
    wval (d.mul d') (e.mul e') = wval d e * wval d' e' := by
  simp only [wval, WData.mul, Q_mul, Int.cast_mul]
  have hd : (d.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d.hD
  have hd' : (d'.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d'.hD
  rw [show ((e.D : ℂ) * e'.D) / (d.D * d'.D) = (e.D / d.D) * (e'.D / d'.D) by field_simp, map_mul]
  ring

theorem phiFun_mul (x y : ratioField N Lc) : phiFun hW (x * y) = phiFun hW x * phiFun hW y := by
  obtain ⟨x, ⟨ρ⟩⟩ := x
  obtain ⟨y, ⟨ρ'⟩⟩ := y
  rw [phiFun_eq hW _ ρ, phiFun_eq hW _ ρ']
  rw [show (⟨x, ⟨ρ⟩⟩ * ⟨y, ⟨ρ'⟩⟩ : ratioField N Lc) = ⟨x * y, ⟨ρ.mul ρ'⟩⟩ from rfl, phiFun_eq hW _ (ρ.mul ρ')]
  rw [phiRep_eq_wval hW (ρ.mul ρ') ((wdata hW ρ.hf).mul (wdata hW ρ'.hf)) ((wdata hW ρ.hg).mul (wdata hW ρ'.hg))]
  exact wval_mul _ _ _ _

def WData.addMul {a b : ℤ} {f g : MF N a} {f' g' : MF N b}
    (d : WData p γ Lc f) (e' : WData p γ Lc g') (d' : WData p γ Lc f') (e : WData p γ Lc g) :
    WData p γ Lc (f.mul g' + (f'.mul g).mcast (add_comm b a)) where
  D := d.D * e'.D * (d'.D * e.D)
  hD := mul_ne_zero (mul_ne_zero d.hD e'.hD) (mul_ne_zero d'.hD e.hD)
  φ := (((d'.D * e.D : ℤ) : Lc)) • d.φ.mul e'.φ + (((d.D * e'.D : ℤ) : Lc)) • (d'.φ.mul e.φ).mcast (add_comm b a)
  hφ := Submodule.add_mem _ (Submodule.smul_mem _ _ (mul_mem_LForms d.hφ e'.hφ))
    (Submodule.smul_mem _ _ (mcast_mem_LForms _ (mul_mem_LForms d'.hφ e.hφ)))
  eq := by
    have h1 : (⇑((f.mul g' + (f'.mul g).mcast (add_comm b a) : MF N (a + b))) : ℍ → ℂ) = ⇑f * ⇑g' + ⇑f' * ⇑g := by
      rw [ModularForm.coe_add, ModularForm.coe_mul]; rfl
    have h2 : (⇑((((d'.D * e.D : ℤ) : Lc)) • d.φ.mul e'.φ +
        (((d.D * e'.D : ℤ) : Lc)) • (d'.φ.mul e.φ).mcast (add_comm b a) : MF N (a + b)) : ℍ → ℂ)
        = ((d'.D * e.D : ℤ) : ℂ) • ((⇑d.φ : ℍ → ℂ) * ⇑e'.φ) + ((d.D * e'.D : ℤ) : ℂ) • ((⇑d'.φ : ℍ → ℂ) * ⇑e.φ) := by
      rw [ModularForm.coe_add, subfield_smul_eq, subfield_smul_eq, ModularForm.IsGLPos.coe_smul,
        ModularForm.IsGLPos.coe_smul, ModularForm.coe_mul]; rfl
    rw [h2, h1, Wfun_add, Wfun_mul, show Wfun p γ (a + b) ((⇑f' : ℍ → ℂ) * ⇑g) = Wfun p γ b ⇑f' * Wfun p γ a ⇑g by
      rw [add_comm, Wfun_mul], d.eq, e.eq, d'.eq, e'.eq]
    ext τ
    simp
    ring

theorem wval_addMul {a b : ℤ} {f g : MF N a} {f' g' : MF N b}
    (d : WData p γ Lc f) (e : WData p γ Lc g) (d' : WData p γ Lc f') (e' : WData p γ Lc g')
    (he : Q e.φ ≠ 0) (he' : Q e'.φ ≠ 0) :
    wval (d.addMul e' d' e) (e.mul e') = wval d e + wval d' e' := by
  simp only [wval, WData.mul, WData.addMul, Q_mul, Q_add, Q_mcast, subfield_smul_eq, Q_smul, Int.cast_mul]
  have hd : (d.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d.hD
  have hd' : (d'.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d'.hD
  have hec : (e.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e.hD
  have he'c : (e'.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e'.hD
  have hC : ∀ u v : ℂ, (HahnSeries.C (u * v) : LaurentSeries ℂ) = HahnSeries.C u * HahnSeries.C v :=
    fun u v => map_mul _ u v
  have hCd : ∀ u v : ℂ, (HahnSeries.C (u / v) : LaurentSeries ℂ) = HahnSeries.C u * (HahnSeries.C v)⁻¹ :=
    fun u v => by rw [div_eq_mul_inv, hC, map_inv₀]
  have hCne : ∀ u : ℂ, u ≠ 0 → (HahnSeries.C u : LaurentSeries ℂ) ≠ 0 := fun u hu => (map_ne_zero HahnSeries.C).mpr hu
  have h1 := hCne _ hd; have h2 := hCne _ hd'; have h3 := hCne _ hec; have h4 := hCne _ he'c
  push_cast
  simp only [hCd, hC]
  field_simp

theorem phiFun_add (x y : ratioField N Lc) : phiFun hW (x + y) = phiFun hW x + phiFun hW y := by
  obtain ⟨x, ⟨ρ⟩⟩ := x
  obtain ⟨y, ⟨ρ'⟩⟩ := y
  rw [phiFun_eq hW _ ρ, phiFun_eq hW _ ρ']
  rw [show (⟨x, ⟨ρ⟩⟩ + ⟨y, ⟨ρ'⟩⟩ : ratioField N Lc) = ⟨x + y, ⟨ρ.add ρ'⟩⟩ from rfl, phiFun_eq hW _ (ρ.add ρ')]
  rw [phiRep_eq_wval hW (ρ.add ρ') ((wdata hW ρ.hf).addMul (wdata hW ρ'.hg) (wdata hW ρ'.hf) (wdata hW ρ.hg))
    ((wdata hW ρ.hg).mul (wdata hW ρ'.hg)),
    ]
  exact wval_addMul _ _ _ _ ((wdata hW ρ.hg).Q_ne_zero ρ.hQg) ((wdata hW ρ'.hg).Q_ne_zero ρ'.hQg)

def WData.one : WData p γ Lc (1 : MF N 0) where
  D := 1
  hD := one_ne_zero
  φ := 1
  hφ := one_mem_LForms
  eq := by
    ext τ
    simp [Wfun, ModularForm.one_coe_eq_one, ModularForm.is_invariant_one]

theorem phiFun_one : phiFun hW 1 = 1 := by
  rw [show (1 : ratioField N Lc) = ⟨1, ⟨Rep.one⟩⟩ from rfl, phiFun_eq hW _ Rep.one,
    phiRep_eq_wval hW Rep.one WData.one WData.one, wval]
  simp [WData.one, Rep.one, Q_one]

theorem phiFun_zero : phiFun hW 0 = 0 := by
  have h := phiFun_add hW 0 0
  rw [add_zero] at h
  linear_combination -h

def phiHom : ratioField N Lc →+* LaurentSeries ℂ where
  toFun := phiFun hW
  map_one' := phiFun_one hW
  map_mul' := phiFun_mul hW
  map_zero' := phiFun_zero hW
  map_add' := phiFun_add hW

theorem phiHom_apply {x : LaurentSeries ℂ} (hx : x ∈ ratioField N Lc) (ρ : Rep (N := N) Lc x) :
    phiHom hW ⟨x, hx⟩ = phiRep hW ρ := phiFun_eq hW hx ρ

theorem phiHom_mem (x : ratioField N Lc) : phiHom hW x ∈ ratioField N Lc := by
  obtain ⟨x, ⟨ρ⟩⟩ := x
  rw [phiHom_apply hW _ ρ, phiRep, wval]
  set d := wdata hW ρ.hf
  set e := wdata hW ρ.hg
  have hq : ((e.D : ℂ) / d.D) ∈ Lc := by
    exact div_mem (intCast_mem Lc e.D) (intCast_mem Lc d.D)
  have : HahnSeries.C ((e.D : ℂ) / d.D) * Q d.φ = Q ((⟨_, hq⟩ : Lc) • d.φ) := by
    rw [subfield_smul_eq, Q_smul]
  rw [this]
  exact div_mem_ratioField (Submodule.smul_mem _ _ d.hφ) e.hφ (e.Q_ne_zero ρ.hQg)

end Phi

section Involution

variable {p : ℕ} [NeZero p] {γ γ' : SL(2, ℤ)} {Lc : Subfield ℂ} (hW : WPHyp N p γ Lc) (hW' : WPHyp N p γ' Lc)

theorem Q_eq_of_coe_eq_smul {k : ℤ} {φ f : MF N k} {c : ℂ} (h : (⇑φ : ℍ → ℂ) = c • ⇑f) : Q φ = HahnSeries.C c * Q f := by
  have : φ = c • f := DFunLike.coe_injective (by
    show (⇑φ : ℍ → ℂ) = ⇑(c • f); rw [h, ModularForm.IsGLPos.coe_smul])
  rw [this, Q_smul]

theorem C_mem_ratioField (c : Lc) : (HahnSeries.C (c : ℂ) : LaurentSeries ℂ) ∈ ratioField N Lc := by
  have : (HahnSeries.C (c : ℂ) : LaurentSeries ℂ) = Q (c • (1 : MF N 0)) / Q (1 : MF N 0) := by
    rw [subfield_smul_eq, Q_smul, Q_one, mul_one, div_one]
  rw [this]
  exact div_mem_ratioField (Submodule.smul_mem _ _ one_mem_LForms) one_mem_LForms (by rw [Q_one]; exact one_ne_zero)

def WData.const (c : Lc) : WData p γ Lc (c • (1 : MF N 0)) where
  D := 1
  hD := one_ne_zero
  φ := c • 1
  hφ := Submodule.smul_mem _ _ one_mem_LForms
  eq := by
    rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, Wfun_smul, Int.cast_one, one_smul]
    congr 1
    ext τ
    simp [Wfun, ModularForm.one_coe_eq_one, ModularForm.is_invariant_one]

theorem phiHom_C (c : Lc) : phiHom hW ⟨HahnSeries.C (c : ℂ), C_mem_ratioField c⟩ = HahnSeries.C (c : ℂ) := by
  have ρ : Rep (N := N) Lc (HahnSeries.C (c : ℂ)) := ⟨0, c • 1, 1, Submodule.smul_mem _ _ one_mem_LForms, one_mem_LForms,
    by rw [Q_one]; exact one_ne_zero, by rw [subfield_smul_eq, Q_smul, Q_one]⟩
  rw [phiHom_apply hW _ ⟨0, c • 1, 1, Submodule.smul_mem _ _ one_mem_LForms, one_mem_LForms,
    by rw [Q_one]; exact one_ne_zero, by rw [subfield_smul_eq, Q_smul, Q_one]⟩,
    phiRep_eq_wval hW _ (WData.const c) WData.one, wval]
  simp [WData.const, WData.one, Q_one, subfield_smul_eq, Q_smul]

variable (u : ℤ → ℂ) (hcomp : ∀ (k : ℤ) (h : ℍ → ℂ), Wfun p γ' k (Wfun p γ k h) = u k • h)
include hcomp

theorem phiHom_phiHom (x : ratioField N Lc) : phiHom hW' ⟨phiHom hW x, phiHom_mem hW x⟩ = x := by
  obtain ⟨x, ⟨ρ⟩⟩ := x
  show _ = x
  set d := wdata hW ρ.hf
  set e := wdata hW ρ.hg
  have hq : ((e.D : ℂ) / d.D) ∈ Lc := div_mem (intCast_mem Lc e.D) (intCast_mem Lc d.D)
  have hdφ : (⟨_, hq⟩ : Lc) • d.φ ∈ LForms Lc ρ.k := Submodule.smul_mem _ _ d.hφ
  have hval : phiHom hW ⟨x, ⟨ρ⟩⟩ = Q ((⟨_, hq⟩ : Lc) • d.φ) / Q e.φ := by
    rw [phiHom_apply hW _ ρ, phiRep, subfield_smul_eq, Q_smul]; rfl

  let ρ₂ : Rep (N := N) Lc (phiHom hW ⟨x, ⟨ρ⟩⟩) :=
    ⟨ρ.k, (⟨_, hq⟩ : Lc) • d.φ, e.φ, hdφ, e.hφ, e.Q_ne_zero ρ.hQg, by rw [hval, div_mul_cancel₀ _ (e.Q_ne_zero ρ.hQg)]⟩
  have step : (phiHom hW' ⟨phiHom hW ⟨x, ⟨ρ⟩⟩, phiHom_mem hW _⟩ : LaurentSeries ℂ) = phiRep hW' ρ₂ := phiHom_apply hW' _ ρ₂
  rw [step, phiRep, wval]
  set d₂ := wdata hW' ρ₂.hf
  set e₂ := wdata hW' ρ₂.hg

  have hd₂ : (⇑d₂.φ : ℍ → ℂ) = ((d₂.D : ℂ) * ((e.D : ℂ) / d.D) * d.D * u ρ.k) • ⇑ρ.f := by
    rw [d₂.eq, show (⇑ρ₂.f : ℍ → ℂ) = ((e.D : ℂ) / d.D) • ⇑d.φ from by
      show (⇑((⟨_, hq⟩ : Lc) • d.φ) : ℍ → ℂ) = _; rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul],
      Wfun_smul, d.eq, Wfun_smul, hcomp]
    simp only [smul_smul]
    congr 1
    change _ = (d₂.D : ℂ) * ((e.D : ℂ) / d.D) * d.D * u ρ₂.k
    ring
  have he₂ : (⇑e₂.φ : ℍ → ℂ) = ((e₂.D : ℂ) * e.D * u ρ.k) • ⇑ρ.g := by
    rw [e₂.eq, show (⇑ρ₂.g : ℍ → ℂ) = ⇑e.φ from rfl, e.eq, Wfun_smul, hcomp]
    simp only [smul_smul]
    congr 1
    change _ = (e₂.D : ℂ) * e.D * u ρ₂.k
    ring
  rw [Q_eq_of_coe_eq_smul hd₂, Q_eq_of_coe_eq_smul he₂]
  have hdc : (d.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d.hD
  have hec : (e.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e.hD
  have hd₂c : (d₂.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d₂.hD
  have he₂c : (e₂.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr e₂.hD
  have huc : u ρ.k ≠ 0 := by
    intro h0
    have := he₂; rw [h0, mul_zero, zero_smul] at this
    exact (e₂.Q_ne_zero (e.Q_ne_zero ρ.hQg)) ((Q_eq_zero_iff _).mpr (DFunLike.coe_injective (this.trans ModularForm.coe_zero.symm)))
  have hC : ∀ u v : ℂ, (HahnSeries.C (u * v) : LaurentSeries ℂ) = HahnSeries.C u * HahnSeries.C v := fun u v => map_mul _ u v
  have hCd : ∀ u v : ℂ, (HahnSeries.C (u / v) : LaurentSeries ℂ) = HahnSeries.C u * (HahnSeries.C v)⁻¹ :=
    fun u v => by rw [div_eq_mul_inv, hC, map_inv₀]
  have hCne : ∀ u : ℂ, u ≠ 0 → (HahnSeries.C u : LaurentSeries ℂ) ≠ 0 := fun u hu => (map_ne_zero HahnSeries.C).mpr hu
  have h1 := hCne _ hdc; have h2 := hCne _ hec; have h3 := hCne _ hd₂c; have h4 := hCne _ he₂c; have h5 := hCne _ huc
  have hQg := ρ.hQg
  conv_rhs => rw [ρ.x_eq]
  simp only [hCd, hC]
  field_simp

end Involution

section Embed

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField N))

def emb : K →+* LaurentSeries ℂ := (coeffMap ι).comp (algebraMap K (LaurentSeries L))

theorem emb_apply (x : K) : emb ι K x = coeffMap ι (x : LaurentSeries L) := rfl

omit [CharZero L] in
theorem coeffMap_injective : Function.Injective (coeffMap ι) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff k) h
  exact ι.injective (by simpa using this)

theorem emb_injective : Function.Injective (emb ι K) :=
  (coeffMap_injective ι).comp Subtype.val_injective

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) : coeffMap ι (coeffEmb L x) = coeffEmb ℂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun q => by simp [eq_ratCast]) x

omit [CharZero L] in
theorem coeffMap_algebraMap' (l : L) : coeffMap ι (algebraMap L (LaurentSeries L) l) = HahnSeries.C (ι l) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]; rfl

theorem coeffEmb_intSeriesC (r : PowerSeries ℤ) : coeffEmb ℂ (intSeriesC ℚ r) = intSeriesC ℂ r := by
  ext k
  simp only [coeffEmb, coeffMap_coeff, intSeriesC]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map]
    simp

theorem intSeriesC_ne_zero_iff (r : PowerSeries ℤ) : intSeriesC ℂ r ≠ 0 ↔ intSeriesC ℚ r ≠ 0 := by
  rw [← coeffEmb_intSeriesC]
  exact map_ne_zero_iff _ (coeffMap_injective (algebraMap ℚ ℂ))

abbrev Lc : Subfield ℂ := ι.fieldRange

theorem div_mem_ratioField_of_isIntegral {k : ℤ} {F G : MF N k} {r s : PowerSeries ℤ}
    (hF : IsIntegralQExp F r) (hG : IsIntegralQExp G s) (hs : intSeriesC ℂ s ≠ 0) :
    intSeriesC ℂ r / intSeriesC ℂ s ∈ ratioField N (Lc ι) := by
  rw [← Q_eq_intSeriesC hF, ← Q_eq_intSeriesC hG]
  exact div_mem_ratioField (mem_LForms_of_isIntegral hF) (mem_LForms_of_isIntegral hG) (by rwa [Q_eq_intSeriesC hG])

theorem coeffEmb_mem_ratioField {y : LaurentSeries ℚ} (hy : y ∈ x1FunctionField N) :
    coeffEmb ℂ y ∈ ratioField N (Lc ι) := by
  have : (x1FunctionField N).toSubfield ≤ (ratioField N (Lc ι)).comap (coeffEmb ℂ) := by
    rw [show x1FunctionField N = IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N)) from rfl,
      IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro z (⟨q, rfl⟩ | ⟨k, F, G, r, s', hF, hG, hs, rfl⟩)
    · show coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) q) ∈ ratioField N (Lc ι)
      rw [ModularCurve.algebraMap_apply_eq_single, coeffEmb, coeffMap_single]
      have hq : (algebraMap ℚ ℂ q) ∈ Lc ι := ⟨algebraMap ℚ L q, by simp⟩
      exact C_mem_ratioField (N := N) (⟨_, hq⟩ : Lc ι)
    · show coeffEmb ℂ (intSeriesC ℚ r / intSeriesC ℚ s') ∈ ratioField N (Lc ι)
      rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
      exact div_mem_ratioField_of_isIntegral ι hF hG ((intSeriesC_ne_zero_iff s').mpr hs)
  exact this hy

include hK in

theorem emb_mem_ratioField (x : K) : emb ι K x ∈ ratioField N (Lc ι) := by
  have hx : (x : LaurentSeries L) ∈ laurentBaseChange L (x1FunctionField N) := hK ▸ x.2
  rw [mem_laurentBaseChange_iff] at hx
  rw [emb_apply]
  generalize (x : LaurentSeries L) = z at hx ⊢
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨l, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact C_mem_ratioField (N := N) (⟨ι l, ⟨l, rfl⟩⟩ : Lc ι)
      · rw [coeffMap_coeffEmb]
        exact coeffEmb_mem_ratioField ι hz
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Embed

section Sigma

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField N))
variable {p : ℕ} [NeZero p] {γ : SL(2, ℤ)} (hW : WPHyp N p γ (Lc ι))

abbrev Simg : Subfield (LaurentSeries ℂ) := K.toSubfield.map (coeffMap ι)

omit [CharZero L] in
theorem phiHom_congr {y y' : LaurentSeries ℂ} (hy : y ∈ ratioField N (Lc ι)) (hy' : y' ∈ ratioField N (Lc ι)) (h : y = y') :
    (phiHom hW ⟨y, hy⟩ : LaurentSeries ℂ) = phiHom hW ⟨y', hy'⟩ := by subst h; rfl

omit [CharZero L] in
theorem mem_Simg_iff {y : LaurentSeries ℂ} : y ∈ Simg ι K ↔ ∃ z : K, coeffMap ι (z : LaurentSeries L) = y := by
  simp only [Simg, Subfield.mem_map]
  exact ⟨fun ⟨z, hz, e⟩ => ⟨⟨z, hz⟩, e⟩, fun ⟨z, e⟩ => ⟨z, z.2, e⟩⟩

omit [CharZero L] in
theorem C_mem_Simg (l : L) : (HahnSeries.C (ι l) : LaurentSeries ℂ) ∈ Simg ι K :=
  (mem_Simg_iff ι K).mpr ⟨algebraMap L K l, by
    rw [show ((algebraMap L K l : K) : LaurentSeries L) = algebraMap L (LaurentSeries L) l from rfl, coeffMap_algebraMap']⟩

theorem C_mem_Simg' (c : Lc ι) : (HahnSeries.C (c : ℂ) : LaurentSeries ℂ) ∈ Simg ι K := by
  obtain ⟨c, ⟨l, rfl⟩⟩ := c; exact C_mem_Simg ι K l

include hK in
theorem coeffEmb_mem_K {y : LaurentSeries ℚ} (hy : y ∈ x1FunctionField N) : coeffEmb L y ∈ K := by
  rw [hK]; exact coeffEmb_mem_laurentBaseChange L hy

include hK in

theorem intSeriesC_div_mem_Simg {k : ℤ} {F G : MF N k} {r s : PowerSeries ℤ}
    (hF : IsIntegralQExp F r) (hG : IsIntegralQExp G s) (hs : intSeriesC ℂ s ≠ 0) :
    intSeriesC ℂ r / intSeriesC ℂ s ∈ Simg ι K := by
  refine (mem_Simg_iff ι K).mpr ⟨⟨coeffEmb L (intSeriesC ℚ r / intSeriesC ℚ s), coeffEmb_mem_K K hK ?_⟩, ?_⟩
  · exact intFormRatiosC_subset ℚ _ (mem_intFormRatiosC F G hF hG ((intSeriesC_ne_zero_iff s).mp hs))
  · show coeffMap ι (coeffEmb L _) = _
    rw [coeffMap_coeffEmb, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

include hK in

theorem Q_div_Q_mem_Simg {k : ℤ} {φ ψ : MF N k} (hφ : φ ∈ LForms (Lc ι) k) (hψ : ψ ∈ LForms (Lc ι) k) (hQ : Q ψ ≠ 0) :
    Q φ / Q ψ ∈ Simg ι K := by
  obtain ⟨n, c, F, r, hc, hF, rfl⟩ := exists_Q_eq_sum_of_mem_LForms hφ
  obtain ⟨n', c', F', r', hc', hF', rfl⟩ := exists_Q_eq_sum_of_mem_LForms hψ

  have : ∃ j, intSeriesC ℂ (r' j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ
    rw [Q_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Q_smul, Q_eq_intSeriesC (hF' j), h j, mul_zero]
  obtain ⟨j₀, hj₀⟩ := this
  set s₀ := intSeriesC ℂ (r' j₀)
  have hnum : Q (∑ i, c i • F i) = s₀ * ∑ i, HahnSeries.C (c i) * (intSeriesC ℂ (r i) / s₀) := by
    rw [Q_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Q_smul, Q_eq_intSeriesC (hF i), mul_div_assoc', mul_div_cancel₀ _ hj₀]
  have hden : Q (∑ j, c' j • F' j) = s₀ * ∑ j, HahnSeries.C (c' j) * (intSeriesC ℂ (r' j) / s₀) := by
    rw [Q_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Q_smul, Q_eq_intSeriesC (hF' j), mul_div_assoc', mul_div_cancel₀ _ hj₀]
  rw [hnum, hden, mul_div_mul_left _ _ hj₀]
  refine div_mem (sum_mem fun i _ => mul_mem (C_mem_Simg' ι K ⟨_, hc i⟩) ?_)
    (sum_mem fun j _ => mul_mem (C_mem_Simg' ι K ⟨_, hc' j⟩) ?_)
  · exact intSeriesC_div_mem_Simg ι K hK (hF i) (hF' j₀) hj₀
  · exact intSeriesC_div_mem_Simg ι K hK (hF' j) (hF' j₀) hj₀

def preimg : Subfield (LaurentSeries ℂ) :=
  ((Simg ι K).comap (phiHom hW)).map (ratioField N (Lc ι)).subtype

theorem mem_preimg_iff {y : LaurentSeries ℂ} :
    y ∈ preimg ι K hW ↔ ∃ hy : y ∈ ratioField N (Lc ι), (phiHom hW ⟨y, hy⟩ : LaurentSeries ℂ) ∈ Simg ι K := by
  simp only [preimg, Subfield.mem_map, Subfield.mem_comap]
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩; exact ⟨hz, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨y, hy⟩, h, rfl⟩

include hK in

theorem phiHom_emb_mem (x : K) :
    (phiHom hW ⟨emb ι K x, emb_mem_ratioField ι K hK x⟩ : LaurentSeries ℂ) ∈ Simg ι K := by
  suffices h : emb ι K x ∈ preimg ι K hW by
    obtain ⟨hy, h⟩ := (mem_preimg_iff ι K hW).mp h; exact h
  have hx : (x : LaurentSeries L) ∈ laurentBaseChange L (x1FunctionField N) := hK ▸ x.2
  rw [mem_laurentBaseChange_iff] at hx
  rw [emb_apply]
  generalize (x : LaurentSeries L) = z at hx ⊢

  suffices hgen : Set.range (algebraMap L (LaurentSeries L)) ∪ ⇑(coeffEmb L) '' (x1FunctionField N : Set (LaurentSeries ℚ))
      ⊆ (preimg ι K hW).comap (coeffMap ι) from Subfield.closure_le.mpr hgen hx
  rintro y (⟨l, rfl⟩ | ⟨w, hw, rfl⟩)
  · rw [SetLike.mem_coe, Subfield.mem_comap, coeffMap_algebraMap', mem_preimg_iff]
    refine ⟨C_mem_ratioField (N := N) (⟨ι l, ⟨l, rfl⟩⟩ : Lc ι), ?_⟩
    rw [phiHom_C hW (⟨ι l, ⟨l, rfl⟩⟩ : Lc ι)]
    exact C_mem_Simg ι K l
  · rw [SetLike.mem_coe, Subfield.mem_comap, coeffMap_coeffEmb]

    have hsub : (x1FunctionField N).toSubfield ≤ (preimg ι K hW).comap (coeffEmb ℂ) := by
      rw [show x1FunctionField N = IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N)) from rfl,
        IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro v (⟨q, rfl⟩ | ⟨k, F, G, r, s', hF, hG, hs, rfl⟩)
      · rw [SetLike.mem_coe, Subfield.mem_comap, ModularCurve.algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
          mem_preimg_iff]
        have hq : (algebraMap ℚ ℂ q) ∈ Lc ι := ⟨algebraMap ℚ L q, by simp⟩
        refine ⟨C_mem_ratioField (N := N) (⟨_, hq⟩ : Lc ι), ?_⟩
        rw [phiHom_congr ι hW _ (C_mem_ratioField (N := N) (⟨_, hq⟩ : Lc ι))
          (show (HahnSeries.single 0 ((algebraMap ℚ ℂ) q) : LaurentSeries ℂ) = HahnSeries.C ((⟨_, hq⟩ : Lc ι) : ℂ) from rfl),
          phiHom_C hW]
        exact C_mem_Simg' ι K ⟨_, hq⟩
      · rw [SetLike.mem_coe, Subfield.mem_comap, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, mem_preimg_iff]
        have hs' : intSeriesC ℂ s' ≠ 0 := (intSeriesC_ne_zero_iff s').mpr hs
        refine ⟨div_mem_ratioField_of_isIntegral ι hF hG hs', ?_⟩
        have hQG : Q G ≠ 0 := by rwa [Q_eq_intSeriesC hG]
        let ρ : Rep (N := N) (Lc ι) (intSeriesC ℂ r / intSeriesC ℂ s') :=
          ⟨k, F, G, mem_LForms_of_isIntegral hF, mem_LForms_of_isIntegral hG, hQG,
            by rw [Q_eq_intSeriesC hF, Q_eq_intSeriesC hG, div_mul_cancel₀ _ hs']⟩
        rw [phiHom_apply hW _ ρ, phiRep, wval]
        set d := wdata hW ρ.hf
        set e := wdata hW ρ.hg
        have hq : ((e.D : ℂ) / d.D) ∈ Lc ι := div_mem (intCast_mem _ e.D) (intCast_mem _ d.D)
        rw [mul_div_assoc]
        exact mul_mem (C_mem_Simg' ι K ⟨_, hq⟩) (Q_div_Q_mem_Simg ι K hK d.hφ e.hφ (e.Q_ne_zero hQG))
    exact hsub hw

def sigmaFun (x : K) : K :=
  ((mem_Simg_iff ι K).mp (phiHom_emb_mem ι K hK hW x)).choose

theorem emb_sigmaFun (x : K) :
    emb ι K (sigmaFun ι K hK hW x) = phiHom hW ⟨emb ι K x, emb_mem_ratioField ι K hK x⟩ :=
  ((mem_Simg_iff ι K).mp (phiHom_emb_mem ι K hK hW x)).choose_spec

def sigmaHom : K →+* K where
  toFun := sigmaFun ι K hK hW
  map_one' := emb_injective ι K (by
    rw [emb_sigmaFun, phiHom_congr ι hW _ (one_mem _) (map_one _), map_one]
    exact (phiHom hW).map_one)
  map_mul' x y := emb_injective ι K (by
    rw [emb_sigmaFun, phiHom_congr ι hW _ (mul_mem (emb_mem_ratioField ι K hK x) (emb_mem_ratioField ι K hK y)) (map_mul _ _ _),
      map_mul (emb ι K), emb_sigmaFun, emb_sigmaFun]
    exact (phiHom hW).map_mul ⟨_, emb_mem_ratioField ι K hK x⟩ ⟨_, emb_mem_ratioField ι K hK y⟩)
  map_zero' := emb_injective ι K (by
    rw [emb_sigmaFun, phiHom_congr ι hW _ (zero_mem _) (map_zero _), map_zero]
    exact (phiHom hW).map_zero)
  map_add' x y := emb_injective ι K (by
    rw [emb_sigmaFun, phiHom_congr ι hW _ (add_mem (emb_mem_ratioField ι K hK x) (emb_mem_ratioField ι K hK y)) (map_add _ _ _),
      map_add (emb ι K), emb_sigmaFun, emb_sigmaFun]
    exact (phiHom hW).map_add ⟨_, emb_mem_ratioField ι K hK x⟩ ⟨_, emb_mem_ratioField ι K hK y⟩)

theorem sigmaHom_apply (x : K) : sigmaHom ι K hK hW x = sigmaFun ι K hK hW x := rfl

theorem sigmaHom_algebraMap (l : L) : sigmaHom ι K hK hW (algebraMap L K l) = algebraMap L K l := by
  apply emb_injective ι K
  have h : emb ι K (algebraMap L K l) = HahnSeries.C (ι l) := by
    rw [emb_apply]; exact coeffMap_algebraMap' ι l
  rw [sigmaHom_apply, emb_sigmaFun, phiHom_congr ι hW _ (C_mem_ratioField (N := N) (⟨ι l, ⟨l, rfl⟩⟩ : Lc ι)) h, h]
  exact phiHom_C hW (⟨ι l, ⟨l, rfl⟩⟩ : Lc ι)

variable {γ' : SL(2, ℤ)} (hW' : WPHyp N p γ' (Lc ι))
  (u : ℤ → ℂ) (hcomp : ∀ (k : ℤ) (h : ℍ → ℂ), Wfun p γ' k (Wfun p γ k h) = u k • h)

include hcomp in
theorem sigmaHom_sigmaHom (x : K) : sigmaHom ι K hK hW' (sigmaHom ι K hK hW x) = x := by
  apply emb_injective ι K
  rw [sigmaHom_apply, sigmaHom_apply, emb_sigmaFun,
    phiHom_congr ι hW' _ (phiHom_mem hW _) (emb_sigmaFun ι K hK hW x)]
  exact phiHom_phiHom hW hW' u hcomp ⟨emb ι K x, emb_mem_ratioField ι K hK x⟩

variable (u' : ℤ → ℂ) (hcomp' : ∀ (k : ℤ) (h : ℍ → ℂ), Wfun p γ k (Wfun p γ' k h) = u' k • h)

include hcomp hcomp' in

def sigma : K ≃ₐ[L] K :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (sigmaHom ι K hK hW) (sigmaHom ι K hK hW')
      (RingHom.ext fun x => sigmaHom_sigmaHom ι K hK hW' hW u' hcomp' x)
      (RingHom.ext fun x => sigmaHom_sigmaHom ι K hK hW hW' u hcomp x))
    (fun l => sigmaHom_algebraMap ι K hK hW l)

include hcomp hcomp' in
theorem emb_sigma (x : K) :
    emb ι K (sigma ι K hK hW hW' u hcomp u' hcomp' x) = phiHom hW ⟨emb ι K x, emb_mem_ratioField ι K hK x⟩ :=
  emb_sigmaFun ι K hK hW x

include hK hcomp hcomp' in

theorem generatorLaw {k : ℤ} (f g : MF N k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (x : K) (hx : (x : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) :
    ∃ (φf φg : MF N k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
      (⇑φf : ℍ → ℂ) = (Df : ℂ) • Wfun p γ k ⇑f ∧ (⇑φg : ℍ → ℂ) = (Dg : ℂ) • Wfun p γ k ⇑g ∧
      (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ),
          (∀ i, IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
      (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ),
          (∀ i, IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
      coeffMap ι ((sigma ι K hK hW hW' u hcomp u' hcomp' x : K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
          ofPowerSeries ℤ ℂ (qExpansion 1 ⇑φg) = HahnSeries.C (Dg : ℂ) * ofPowerSeries ℤ ℂ (qExpansion 1 ⇑φf) := by
  have hQg : Q g ≠ 0 := by rw [Q_eq_intSeriesC hg]; exact (intSeriesC_ne_zero_iff pg).mpr hg0
  have hex : emb ι K x = Q f / Q g := by
    rw [emb_apply, hx, coeffMap_coeffEmb, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, Q_eq_intSeriesC hf,
      Q_eq_intSeriesC hg]
  let ρ : Rep (N := N) (Lc ι) (Q f / Q g) :=
    ⟨k, f, g, mem_LForms_of_isIntegral hf, mem_LForms_of_isIntegral hg, hQg, div_mul_cancel₀ _ hQg⟩
  have hval : emb ι K (sigma ι K hK hW hW' u hcomp u' hcomp' x) = wval (wdata hW ρ.hf) (wdata hW ρ.hg) := by
    rw [emb_sigma, phiHom_congr ι hW _ (div_mem_ratioField (mem_LForms_of_isIntegral hf) (mem_LForms_of_isIntegral hg) hQg) hex,
      phiHom_apply hW _ ρ, phiRep]
  set d := wdata hW ρ.hf
  set e := wdata hW ρ.hg
  have span_of : ∀ {φ : MF N k}, φ ∈ LForms (Lc ι) k →
      ∃ (n : ℕ) (c : Fin n → L) (F : Fin n → MF N k) (r : Fin n → PowerSeries ℤ),
        (∀ i, IsIntegralQExp (F i) (r i)) ∧ φ = ∑ i, (ι (c i)) • F i := by
    intro φ hφ
    obtain ⟨n, c, F, r, hc, hF, hφ'⟩ := exists_Q_eq_sum_of_mem_LForms hφ
    choose l hl using hc
    refine ⟨n, l, F, r, hF, ?_⟩
    rw [hφ']
    exact Finset.sum_congr rfl (fun i _ => by rw [hl i])
  refine ⟨d.φ, e.φ, d.D, e.D, d.hD, e.hD, d.eq, e.eq, span_of d.hφ, span_of e.hφ, ?_⟩
  have hQe : Q e.φ ≠ 0 := e.Q_ne_zero hQg
  have hD : (d.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d.hD
  have h := hval
  rw [wval, emb_apply] at h
  show coeffMap ι _ * HahnSeries.C (d.D : ℂ) * Q e.φ = HahnSeries.C (e.D : ℂ) * Q d.φ
  rw [h, div_mul_eq_mul_div, div_mul_cancel₀ _ hQe, mul_comm (HahnSeries.C _ * Q d.φ), ← mul_assoc, ← map_mul,
    mul_div_cancel₀ _ hD]

end Sigma

section Value

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField N))
variable {p : ℕ} [NeZero p] {γ : SL(2, ℤ)} (hW : WPHyp N p γ (Lc ι))

theorem coeffEmb_jq_eq_jqModC : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat, coeffEmb]; exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_qExpand (M₀ : ℕ) [NeZero M₀] (R : Type) [Field R] [Algebra ℚ R] (x : LaurentSeries ℚ) :
    coeffEmb R (qExpand ℚ M₀ x) = qExpand R M₀ (coeffEmb R x) := by
  ext k
  by_cases hk : (M₀ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd M₀ _ hk, qExpand_coeff_of_not_dvd M₀ _ hk, map_zero]

theorem phiHom_jqModC :
    ∃ hj : jqModC ℂ ∈ ratioField N (Lc ι), (phiHom hW ⟨jqModC ℂ, hj⟩ : LaurentSeries ℂ) = qExpand ℂ p (jqModC ℂ) := by
  classical
  obtain ⟨k, A, B, pA, pB, hA, hB, hB0, hjq⟩ := ModularCurve.jqModC_mem_intFormRatiosC ℂ (⊤ : Subgroup SL(2, ℤ))
  have hle : Γ1 N ≤ ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono le_top
  let A₁ : MF N k := restrictForm hle A
  let B₁ : MF N k := restrictForm hle B
  have hA₁ : IsIntegralQExp A₁ pA := hA
  have hB₁ : IsIntegralQExp B₁ pB := hB
  have hQB : Q B₁ ≠ 0 := by rwa [Q_eq_intSeriesC hB₁]
  have hQA : Q A₁ = intSeriesC ℂ pA := Q_eq_intSeriesC hA₁
  have hmem : jqModC ℂ ∈ ratioField N (Lc ι) := by rw [hjq]; exact div_mem_ratioField_of_isIntegral ι hA₁ hB₁ hB0
  refine ⟨hmem, ?_⟩
  let ρ : Rep (N := N) (Lc ι) (jqModC ℂ) :=
    ⟨k, A₁, B₁, mem_LForms_of_isIntegral hA₁, mem_LForms_of_isIntegral hB₁, hQB,
      by rw [hjq, Q_eq_intSeriesC hA₁, Q_eq_intSeriesC hB₁, div_mul_cancel₀ _ hB0]⟩

  have mkD : ∀ (F : ModularForm (((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (r : PowerSeries ℤ)
      (hF : IsIntegralQExp (restrictForm hle F) r),
      ∃ d : WData p γ (Lc ι) (restrictForm hle F), d.D = 1 ∧
        Q d.φ = qExpand ℂ p (intSeriesC ℂ r) := by
    intro F r hF
    let d₀ := wdata hW (mem_LForms_of_isIntegral hF)
    have hDc : (d₀.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d₀.hD
    have hinv : ((d₀.D : ℂ))⁻¹ ∈ Lc ι := inv_mem (intCast_mem _ d₀.D)

    have hWF : Wfun p γ k (⇑(restrictForm hle F) : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix p • τ) := by
      ext τ
      simp only [Wfun, coe_restrictForm]
      have hγmem : (γ : GL (Fin 2) ℝ) ∈ (((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
        Subgroup.mem_map.mpr ⟨γ, Subgroup.mem_top γ, rfl⟩
      rw [ModularForm.SL_slash, SlashInvariantForm.slash_action_eqn F (γ : GL (Fin 2) ℝ) hγmem]
    refine ⟨⟨1, one_ne_zero, (⟨_, hinv⟩ : Lc ι) • d₀.φ, Submodule.smul_mem _ _ d₀.hφ, ?_⟩, rfl, ?_⟩
    · rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, Int.cast_one, one_smul]
      simp [inv_mul_cancel₀ hDc]
    · show Q ((⟨_, hinv⟩ : Lc ι) • d₀.φ) = _

      have hcoe : (⇑((⟨_, hinv⟩ : Lc ι) • d₀.φ) : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix p • τ) := by
        rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, ← hWF]
        simp [inv_mul_cancel₀ hDc]
      rw [Q, hcoe]
      have h213 := ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne p
        (F.mcast rfl (MonoidHom.range_eq_map _))
      have hcF : ((F.mcast rfl (MonoidHom.range_eq_map _) : ModularForm 𝒮ℒ k) : ℍ → ℂ) = ⇑F := rfl
      rw [hcF] at h213
      rw [show (ofPowerSeries ℤ ℂ (qExpansion 1 fun τ : ℍ => F (ModularForm.heckeDiagMatrix p • τ)))
          = ((qExpansion 1 fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix p • τ) : PowerSeries ℂ) : LaurentSeries ℂ) from rfl,
        h213]
      congr 1
      have : IsIntegralQExp (⇑F) r := hF
      rw [intSeriesC, ← this]
  obtain ⟨dA, hdA, hQdA⟩ := mkD A pA hA₁
  obtain ⟨dB, hdB, hQdB⟩ := mkD B pB hB₁
  rw [phiHom_apply hW hmem ρ, phiRep_eq_wval hW ρ dA dB, wval, hdA, hdB, hQdA, hQdB, hjq, map_div₀]
  simp

include hK in

theorem coe_sigmaFun_j (j : K) (hj : (j : LaurentSeries L) = coeffEmb L jq) :
    ((sigmaFun ι K hK hW j : K) : LaurentSeries L) = coeffEmb L (qExpand ℚ p jq) := by
  apply coeffMap_injective ι
  have hej : emb ι K j = jqModC ℂ := by rw [emb_apply, hj, coeffMap_coeffEmb, coeffEmb_jq_eq_jqModC]
  obtain ⟨hmem, hval⟩ := phiHom_jqModC ι hW
  rw [← emb_apply, emb_sigmaFun, phiHom_congr ι hW _ hmem hej, hval, coeffMap_coeffEmb, coeffEmb_qExpand,
    coeffEmb_jq_eq_jqModC]

end Value

section Comp

variable {p : ℕ} [NeZero p]

theorem Wfun_eq_smul_slash (g : SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) :
    Wfun p g k F = ((p : ℂ) ^ (k - 1))⁻¹ • (F ∣[k] ((g : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  ext τ
  simp only [Wfun, Pi.smul_apply, smul_eq_mul]
  rw [SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p), ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hp0), one_mul, ModularForm.SL_slash]

theorem Wfun_Wfun_of_mul_eq_scalar (γ γ' : SL(2, ℤ)) (u : ℝˣ) (hu : (u : ℝ) = p)
    (hmat : ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) u)
    (k : ℤ) (h : ℍ → ℂ) : Wfun p γ' k (Wfun p γ k h) = ((p : ℂ) ^ k)⁻¹ • h := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val = (u : ℝ) * u := by
    simp [Matrix.GeneralLinearGroup.scalar, sq]
  have hdetpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by
    rw [hdet, hu]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p) |> fun h => Nat.mul_pos h h
  rw [Wfun_eq_smul_slash γ, Wfun_smul, Wfun_eq_smul_slash γ', ← SlashAction.slash_mul, hmat]
  ext τ
  rw [Pi.smul_apply, Pi.smul_apply, ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, hdet, hu, ContinuousAlgEquiv.refl_apply,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) * p)]
  simp only [smul_eq_mul]
  push_cast
  rw [show ((p : ℂ) * p) ^ (k - 1) = (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1) from mul_zpow _ _ _]
  have hz : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hp0
  have hzk : (p : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hp0
  rw [zpow_neg, ← inv_zpow, inv_zpow', zpow_neg]
  field_simp
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end Comp

section Concrete

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]

theorem exists_bezout (hpM : ¬ p ∣ M) : ∃ x y : ℤ, x * p - y * M = 1 := by
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (p : ℤ) (M : ℤ))
  exact ⟨a, -b, by linear_combination hab⟩

def bzX (hpM : ¬ p ∣ M) : ℤ := (exists_bezout p M hpM).choose
def bzY (hpM : ¬ p ∣ M) : ℤ := (exists_bezout p M hpM).choose_spec.choose
theorem bz_spec (hpM : ¬ p ∣ M) : bzX p M hpM * p - bzY p M hpM * M = 1 := (exists_bezout p M hpM).choose_spec.choose_spec

def γW (hpM : ¬ p ∣ M) : SL(2, ℤ) := ⟨!![bzX p M hpM, bzY p M hpM; (M : ℤ), (p : ℤ)], by
  rw [Matrix.det_fin_two_of]; linear_combination bz_spec p M hpM⟩

def γW' (hpM : ¬ p ∣ M) : SL(2, ℤ) := ⟨!![(1 : ℤ), -bzY p M hpM; -(M : ℤ), bzX p M hpM * p], by
  rw [Matrix.det_fin_two_of]; linear_combination bz_spec p M hpM⟩

theorem γW_mem (hpM : ¬ p ∣ M) : γW p M hpM ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem]; simp [γW]

theorem γW'_mem (hpM : ¬ p ∣ M) : γW' p M hpM ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem]; simp [γW']

theorem γW_dvd (hpM : ¬ p ∣ M) : (p : ℤ) ∣ (γW p M hpM) 1 1 := by simp [γW]

theorem γW'_dvd (hpM : ¬ p ∣ M) : (p : ℤ) ∣ (γW' p M hpM) 1 1 := by simp [γW']

def pUnit : ℝˣ := Units.mk0 (p : ℝ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

theorem mul_eq_scalar (hpM : ¬ p ∣ M) :
    ((γW p M hpM : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γW' p M hpM : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (pUnit p) := by
  have hb : (bzX p M hpM : ℝ) * p - (bzY p M hpM : ℝ) * M = 1 := by exact_mod_cast bz_spec p M hpM
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
  fin_cases i <;> fin_cases j <;>
    simp [γW, γW', Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.scalar_apply, ModularForm.val_heckeDiagMatrix hp0,
      pUnit, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, Matrix.natCast_apply] <;>
    first | ring1 | linear_combination (p : ℝ) * hb

theorem mul_eq_scalar' (hpM : ¬ p ∣ M) :
    ((γW' p M hpM : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γW p M hpM : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (pUnit p) := by
  have hb : (bzX p M hpM : ℝ) * p - (bzY p M hpM : ℝ) * M = 1 := by exact_mod_cast bz_spec p M hpM
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
  fin_cases i <;> fin_cases j <;>
    simp [γW, γW', Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.scalar_apply, ModularForm.val_heckeDiagMatrix hp0,
      pUnit, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, Matrix.natCast_apply] <;>
    first | ring1 | linear_combination (p : ℝ) * hb

variable (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]

def ιC : L →+* ℂ :=
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L
  (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom

theorem adjoin_exp_le (c : ℂ) (hc : c ∈ IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)) :
    c ∈ (ιC p L).fieldRange := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hζL := IsCyclotomicExtension.zeta_spec p ℚ L
  have hζ : IsPrimitiveRoot (ιC p L (IsCyclotomicExtension.zeta p ℚ L)) p := hζL.map_of_injective (ιC p L).injective
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ^ p = 1 :=
    (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).pow_eq_one
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hexp
  have hmem : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ∈ (ιC p L).fieldRange := by
    rw [← hi, ← map_pow]; exact ⟨_, rfl⟩

  have hle : (IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)).toSubfield
      ≤ (ιC p L).fieldRange := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro z (⟨q, rfl⟩ | hz)
    · exact ⟨algebraMap ℚ L q, by simp [ιC]⟩
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hmem
  exact hle hc

theorem wpHyp (hpM : ¬ p ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    WPHyp (M * p) p γ (Lc (ιC p L)) := by
  intro k f p₀ hf
  obtain ⟨D, n, c, F, r, hD, hc, hF, heq⟩ :=
    ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul p M hpM f hf γ hγ hγp
  exact ⟨D, n, c, F, r, hD, fun i => adjoin_exp_le p L _ (hc i), hF, heq⟩

end Concrete

end INVOL
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

namespace INVOL

section Degen

open scoped Pointwise Manifold

theorem exists_mapGL_mul_heckeDiagMatrix_eq (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 d) :
    ∃ γ' : SL(2, ℤ),
      Matrix.SpecialLinearGroup.mapGL ℝ γ' * ModularForm.heckeDiagMatrix d
        = ModularForm.heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have hp : d ≠ 0 := NeZero.ne d
  obtain ⟨c, hc⟩ : (d : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) d).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc] at hdet
  refine ⟨⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (d : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · apply Units.ext
    simp only [Units.val_mul, ModularForm.val_heckeDiagMatrix hp,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hc] <;> ring

theorem gamma0_le_conj (d : ℕ) [NeZero d] :
    (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))
      ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix d)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨γ', hγ'⟩ := exists_mapGL_mul_heckeDiagMatrix_eq d γ hγ
  refine ⟨γ', ?_⟩
  rw [← hγ', mul_inv_cancel_right]

theorem diag_slash_eq_self (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))) :
    ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) ∣[k] γ = (⇑F) ∣[k] ModularForm.heckeDiagMatrix d := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact SlashInvariantFormClass.slash_action_eq (ModularForm.translate F (ModularForm.heckeDiagMatrix d)) γ
    (gamma0_le_conj d hγ)

theorem diag_holo (d : ℕ) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact ModularFormClass.holo (ModularForm.translate F (ModularForm.heckeDiagMatrix d))

theorem diag_bdd_at_cusps (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) {c : OnePoint ℝ}
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) k := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact ModularFormClass.bdd_at_cusps (ModularForm.translate F (ModularForm.heckeDiagMatrix d)) (hc.mono (gamma0_le_conj d))

def diagForm (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ModularForm (CongruenceSubgroup.Gamma0 d) k where
  toFun := (⇑F) ∣[k] ModularForm.heckeDiagMatrix d
  slash_action_eq' γ hγ := diag_slash_eq_self d F γ hγ
  holo' := diag_holo d F
  bdd_at_cusps' hc := diag_bdd_at_cusps d F hc

theorem coe_diagForm (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ⇑(diagForm d F) = (⇑F) ∣[k] ModularForm.heckeDiagMatrix d := rfl

theorem diagForm_apply (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) (τ : ℍ) :
    diagForm d F τ = (d : ℂ) ^ (k - 1) * F (ModularForm.heckeDiagMatrix d • τ) :=
  ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne d) ⇑F τ

theorem heckeDiagMatrix_smul_smul (d e : ℕ) [NeZero d] [NeZero e] (τ : ℍ) :
    ModularForm.heckeDiagMatrix d • ModularForm.heckeDiagMatrix e • τ = ModularForm.heckeDiagMatrix (d * e) • τ := by
  haveI : NeZero (d * e) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne e)⟩
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne d), ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne e),
    ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne (d * e))]
  push_cast; ring

theorem gamma1_le_gamma0 {N : ℕ} (d : ℕ) (hd : d ∣ N) :
    Γ1 N ≤ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)) := by
  refine Subgroup.map_mono ?_
  intro γ hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
  exact (Int.natCast_dvd_natCast.mpr hd).trans h0

def spread (d : ℕ) (r : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if d ∣ n then PowerSeries.coeff (n / d) r else 0

theorem intSeriesC_spread (d : ℕ) [NeZero d] (R : Type) [Field R] (r : PowerSeries ℤ) :
    intSeriesC R (spread d r) = qExpand R d (intSeriesC R r) := by
  have hd : d ≠ 0 := NeZero.ne d
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    by_cases hdk : (d : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hdk
      rw [qExpand_coeff_mul, intSeriesC, ModularCurve.ofPowerSeries_coeff_of_neg]
      have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      by_contra hm
      push Not at hm
      exact absurd hk (not_lt.mpr (mul_nonneg hd0.le hm))
    · rw [qExpand_coeff_of_not_dvd d _ hdk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, spread, PowerSeries.coeff_mk]
    by_cases hdn : d ∣ n
    · obtain ⟨m, rfl⟩ := hdn
      rw [if_pos (dvd_mul_right d m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd),
        show ((d * m : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) by push_cast; ring, qExpand_coeff_mul, intSeriesC,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    · rw [if_neg hdn, map_zero, qExpand_coeff_of_not_dvd d]
      intro h
      exact hdn (Int.natCast_dvd_natCast.mp h)

theorem isIntegralQExp_comp_heckeDiagMatrix (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) {r : PowerSeries ℤ}
    (hF : IsIntegralQExp (⇑F) r) :
    IsIntegralQExp (fun τ : ℍ => F (ModularForm.heckeDiagMatrix d • τ)) (spread d r) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  change intSeriesC ℂ (spread d r) = ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix d • τ)) : PowerSeries ℂ) : LaurentSeries ℂ)
  rw [intSeriesC_spread, ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne d F]
  congr 1
  change _ = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F)
  rw [intSeriesC, hF]

variable {N : ℕ}

theorem exists_coe_eq_comp_heckeDiagMatrix (d : ℕ) [NeZero d] (hd : d ∣ N) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ Fd : MF N k, (⇑Fd : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix d • τ) := by
  have hdC : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ • restrictForm (gamma1_le_gamma0 d hd) (diagForm d F), ?_⟩
  ext τ
  rw [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, coe_restrictForm, diagForm_apply, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hdC, one_mul]

end Degen
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

section DegenValue

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) [NeZero p]
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
variable (hW : WPHyp (M * p) p (γW p M hpM) (Lc ι))

theorem exists_rep_qExpand_jqModC (e : ℕ) [NeZero e] (he : e ∣ M * p) :
    ∃ (k : ℤ) (A B : ModularForm 𝒮ℒ k) (rA rB : PowerSeries ℤ) (Ae Be : MF (M * p) k),
      IsIntegralQExp (⇑A) rA ∧ IsIntegralQExp (⇑B) rB ∧ intSeriesC ℂ rB ≠ 0 ∧
      jqModC ℂ = intSeriesC ℂ rA / intSeriesC ℂ rB ∧
      (⇑Ae : ℍ → ℂ) = (fun τ => A (ModularForm.heckeDiagMatrix e • τ)) ∧
      (⇑Be : ℍ → ℂ) = (fun τ => B (ModularForm.heckeDiagMatrix e • τ)) ∧
      IsIntegralQExp (⇑Ae) (spread e rA) ∧ IsIntegralQExp (⇑Be) (spread e rB) ∧
      Q Ae = qExpand ℂ e (intSeriesC ℂ rA) ∧ Q Be = qExpand ℂ e (intSeriesC ℂ rB) ∧ Q Be ≠ 0 := by
  classical
  obtain ⟨k, A₀, B₀, pA, pB, hA, hB, hB0, hjq⟩ := ModularCurve.jqModC_mem_intFormRatiosC ℂ (⊤ : Subgroup SL(2, ℤ))
  let A : ModularForm 𝒮ℒ k := A₀.mcast rfl (MonoidHom.range_eq_map _)
  let B : ModularForm 𝒮ℒ k := B₀.mcast rfl (MonoidHom.range_eq_map _)
  obtain ⟨Ae, hAe⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e he A
  obtain ⟨Be, hBe⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e he B
  have hA' : IsIntegralQExp (⇑A) pA := hA
  have hB' : IsIntegralQExp (⇑B) pB := hB
  refine ⟨k, A, B, pA, pB, Ae, Be, ?_⟩
  have hIA : IsIntegralQExp (⇑Ae) (spread e pA) := by rw [hAe]; exact isIntegralQExp_comp_heckeDiagMatrix e A hA'
  have hIB : IsIntegralQExp (⇑Be) (spread e pB) := by rw [hBe]; exact isIntegralQExp_comp_heckeDiagMatrix e B hB'
  have hQA : Q Ae = qExpand ℂ e (intSeriesC ℂ pA) := by rw [Q_eq_intSeriesC hIA, intSeriesC_spread]
  have hQB : Q Be = qExpand ℂ e (intSeriesC ℂ pB) := by rw [Q_eq_intSeriesC hIB, intSeriesC_spread]
  have hQB0 : Q Be ≠ 0 := by rw [hQB]; exact (map_ne_zero_iff _ (qExpand ℂ e).injective).mpr hB0
  exact ⟨hA', hB', hB0, hjq, hAe, hBe, hIA, hIB, hQA, hQB, hQB0⟩

theorem Wfun_comp_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (Fd : MF (M * p) k)
    (hFd : (⇑Fd : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix d • τ)) :
    Wfun p (γW p M hpM) k (⇑Fd) = fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ) := by
  have hdC : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  let G : ModularForm (CongruenceSubgroup.Gamma0 d) k := ((d : ℂ) ^ (k - 1))⁻¹ • diagForm d F
  have hG : (⇑G : ℍ → ℂ) = ⇑Fd := by
    rw [hFd]; ext τ
    show (((d : ℂ) ^ (k - 1))⁻¹ • ⇑(diagForm d F)) τ = _
    rw [Pi.smul_apply, diagForm_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdC, one_mul]
  have hγmem : ((γW p M hpM : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)) := by
    refine Subgroup.mem_map.mpr ⟨γW p M hpM, ?_, rfl⟩
    have h0 := γW_mem p M hpM
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact (Int.natCast_dvd_natCast.mpr hd).trans h0
  ext τ
  simp only [Wfun]
  rw [ModularForm.SL_slash, ← hG, SlashInvariantForm.slash_action_eqn G _ hγmem, hG, hFd]
  show F (ModularForm.heckeDiagMatrix d • ModularForm.heckeDiagMatrix p • τ) = _
  rw [heckeDiagMatrix_smul_smul]

include hpM in

theorem exists_heckeDiagMatrix_mul_γW_eq (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ∃ γ'' : SL(2, ℤ),
      ModularForm.heckeDiagMatrix (d * p) * Matrix.SpecialLinearGroup.mapGL ℝ (γW p M hpM)
        = Matrix.SpecialLinearGroup.mapGL ℝ γ'' *
          ModularForm.upperTriangularGL (d : ℝ) 0 (p : ℝ) (by exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)) := by
  obtain ⟨c, hc⟩ := hd
  have hb := bz_spec p M hpM
  have hp0 : p ≠ 0 := NeZero.ne p
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp0
  have hcM : (M : ℤ) = d * c := by exact_mod_cast hc
  refine ⟨⟨!![bzX p M hpM * p, (d : ℤ) * bzY p M hpM; (c : ℤ), 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hb + bzY p M hpM * hcM
  · have hbR : (bzX p M hpM : ℝ) * p - (bzY p M hpM : ℝ) * M = 1 := by exact_mod_cast hb
    have hcR : (M : ℝ) = d * c := by exact_mod_cast hc
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γW, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hdp0, ModularForm.val_upperTriangularGL,
        Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, hcR] <;>
      first | ring1 | (push_cast; ring1)

theorem Wfun_comp_mul_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (Fdp : MF (M * p) k)
    (hFdp : (⇑Fdp : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ)) :
    Wfun p (γW p M hpM) k (⇑Fdp) = (((p : ℚ) ^ (-k) : ℚ) : ℂ) • fun τ => F (ModularForm.heckeDiagMatrix d • τ) := by
  have hp0 : p ≠ 0 := NeZero.ne p
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp0
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hdpC : ((d : ℂ) * p) ≠ 0 := mul_ne_zero hdC hpC
  obtain ⟨γ'', hγ⟩ := exists_heckeDiagMatrix_mul_γW_eq p M hpM d hd
  set U : GL (Fin 2) ℝ := ModularForm.upperTriangularGL (d : ℝ) 0 (p : ℝ)
    (by exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)) with hU
  have hdetU : U.det.val = (d : ℝ) * p := by
    simp [hU, ModularForm.upperTriangularGL, Matrix.det_fin_two_of]
  have hdetUpos : 0 < U.det.val := by rw [hdetU]; positivity
  have hσU : UpperHalfPlane.σ U = .refl ℝ ℂ := by rw [UpperHalfPlane.σ, if_pos hdetUpos]
  have hσγ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ (γW p M hpM)) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos]
    simp [Matrix.SpecialLinearGroup.mapGL]

  have h1 : (⇑Fdp : ℍ → ℂ) = (((d : ℂ) * p) ^ (k - 1))⁻¹ • ((⇑F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix (d * p)) := by
    ext τ
    rw [hFdp, Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply k hdp0, smul_eq_mul, ← mul_assoc, Nat.cast_mul,
      inv_mul_cancel₀ (zpow_ne_zero _ hdpC), one_mul]

  have hinv : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ'') = ⇑F :=
    SlashInvariantForm.slash_action_eqn F _ ⟨γ'', rfl⟩

  have h2 : (⇑Fdp : ℍ → ℂ) ∣[k] (γW p M hpM) = (((d : ℂ) * p) ^ (k - 1))⁻¹ • ((⇑F : ℍ → ℂ) ∣[k] U) := by
    show (⇑Fdp : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γW p M hpM)) = _
    rw [h1, ModularForm.smul_slash, hσγ, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul, hγ, SlashAction.slash_mul,
      hinv]

  have hUsmul : ∀ τ : ℍ, U • (ModularForm.heckeDiagMatrix p • τ) = ModularForm.heckeDiagMatrix d • τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetUpos, ModularForm.coe_heckeDiagMatrix_smul hd0]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hU, ModularForm.val_upperTriangularGL, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      ModularForm.coe_heckeDiagMatrix_smul hp0]
    push_cast
    field_simp
    ring
  have hden : ∀ τ : ℍ, UpperHalfPlane.denom U ((ModularForm.heckeDiagMatrix p • τ : ℍ) : ℂ) = (p : ℂ) := by
    intro τ
    simp [UpperHalfPlane.denom, hU, ModularForm.val_upperTriangularGL]
  ext τ
  show ((⇑Fdp : ℍ → ℂ) ∣[k] (γW p M hpM)) (ModularForm.heckeDiagMatrix p • τ) = _
  rw [h2, Pi.smul_apply, Pi.smul_apply, ModularForm.slash_apply, hσU, ContinuousAlgEquiv.refl_apply, hdetU, hden, hUsmul,
    abs_of_pos (by positivity : (0 : ℝ) < d * p), smul_eq_mul, smul_eq_mul]
  push_cast
  rw [show (((d : ℂ) * p) ^ (k - 1))⁻¹ * (F (ModularForm.heckeDiagMatrix d • τ) * ((d : ℂ) * p) ^ (k - 1) * (p : ℂ) ^ (-k))
      = ((((d : ℂ) * p) ^ (k - 1))⁻¹ * ((d : ℂ) * p) ^ (k - 1)) * ((p : ℂ) ^ (-k) * F (ModularForm.heckeDiagMatrix d • τ)) by ring,
    inv_mul_cancel₀ (zpow_ne_zero _ hdpC), one_mul]

theorem phiHom_qExpand_jqModC (d : ℕ) [NeZero d] (hd : d ∣ M) :
    haveI : NeZero (d * p) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)⟩
    (∃ hx : qExpand ℂ d (jqModC ℂ) ∈ ratioField (M * p) (Lc ι),
      (phiHom hW ⟨qExpand ℂ d (jqModC ℂ), hx⟩ : LaurentSeries ℂ) = qExpand ℂ (d * p) (jqModC ℂ)) ∧
    (∃ hx : qExpand ℂ (d * p) (jqModC ℂ) ∈ ratioField (M * p) (Lc ι),
      (phiHom hW ⟨qExpand ℂ (d * p) (jqModC ℂ), hx⟩ : LaurentSeries ℂ) = qExpand ℂ d (jqModC ℂ)) := by
  classical
  haveI : NeZero (d * p) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)⟩
  have hdMp : d ∣ M * p := hd.mul_right p
  have hdpMp : d * p ∣ M * p := Nat.mul_dvd_mul_right hd p
  constructor
  ·
    obtain ⟨k, A, B, rA, rB, Ad, Bd, hA, hB, hB0, hjq, hAd, hBd, hIA, hIB, hQA, hQB, hQB0⟩ :=
      exists_rep_qExpand_jqModC p M d hdMp
    have hx : qExpand ℂ d (jqModC ℂ) = Q Ad / Q Bd := by rw [hjq, map_div₀, hQA, hQB]
    have hmem : qExpand ℂ d (jqModC ℂ) ∈ ratioField (M * p) (Lc ι) := by
      rw [hx]; exact div_mem_ratioField (mem_LForms_of_isIntegral hIA) (mem_LForms_of_isIntegral hIB) hQB0
    refine ⟨hmem, ?_⟩
    let ρ : Rep (N := M * p) (Lc ι) (qExpand ℂ d (jqModC ℂ)) :=
      ⟨k, Ad, Bd, mem_LForms_of_isIntegral hIA, mem_LForms_of_isIntegral hIB, hQB0, by rw [hx, div_mul_cancel₀ _ hQB0]⟩

    have mkD : ∀ (F : ModularForm 𝒮ℒ k) (r : PowerSeries ℤ) (Fd : MF (M * p) k), IsIntegralQExp (⇑F) r →
        (⇑Fd : ℍ → ℂ) = (fun τ => F (ModularForm.heckeDiagMatrix d • τ)) → IsIntegralQExp (⇑Fd) (spread d r) →
        ∃ e : WData p (γW p M hpM) (Lc ι) Fd, e.D = 1 ∧ Q e.φ = qExpand ℂ (d * p) (intSeriesC ℂ r) := by
      intro F r Fd hF hFd hIFd
      let d₀ := wdata hW (mem_LForms_of_isIntegral hIFd)
      have hDc : (d₀.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d₀.hD
      have hinv : ((d₀.D : ℂ))⁻¹ ∈ Lc ι := inv_mem (intCast_mem _ d₀.D)
      have hWF := Wfun_comp_of_dvd p M hpM d hd F Fd hFd
      refine ⟨⟨1, one_ne_zero, (⟨_, hinv⟩ : Lc ι) • d₀.φ, Submodule.smul_mem _ _ d₀.hφ, ?_⟩, rfl, ?_⟩
      · rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, Int.cast_one, one_smul]
        simp [inv_mul_cancel₀ hDc]
      · show Q ((⟨_, hinv⟩ : Lc ι) • d₀.φ) = _
        have hcoe : (⇑((⟨_, hinv⟩ : Lc ι) • d₀.φ) : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ) := by
          rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, hWF]
          simp [inv_mul_cancel₀ hDc]
        obtain ⟨Fdp, hFdp⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) (d * p) hdpMp F
        have hI := isIntegralQExp_comp_heckeDiagMatrix (d * p) F hF
        rw [← hFdp] at hI hcoe
        have : (⟨_, hinv⟩ : Lc ι) • d₀.φ = Fdp := DFunLike.ext' hcoe
        rw [this, Q_eq_intSeriesC hI, intSeriesC_spread]
    obtain ⟨dA, hdA, hQdA⟩ := mkD A rA Ad hA hAd hIA
    obtain ⟨dB, hdB, hQdB⟩ := mkD B rB Bd hB hBd hIB
    rw [phiHom_apply hW hmem ρ, phiRep_eq_wval hW ρ dA dB, wval, hdA, hdB, hQdA, hQdB, hjq, map_div₀]
    simp
  ·
    obtain ⟨k, A, B, rA, rB, Adp, Bdp, hA, hB, hB0, hjq, hAdp, hBdp, hIA, hIB, hQA, hQB, hQB0⟩ :=
      exists_rep_qExpand_jqModC p M (d * p) hdpMp
    have hx : qExpand ℂ (d * p) (jqModC ℂ) = Q Adp / Q Bdp := by rw [hjq, map_div₀, hQA, hQB]
    have hmem : qExpand ℂ (d * p) (jqModC ℂ) ∈ ratioField (M * p) (Lc ι) := by
      rw [hx]; exact div_mem_ratioField (mem_LForms_of_isIntegral hIA) (mem_LForms_of_isIntegral hIB) hQB0
    refine ⟨hmem, ?_⟩
    let ρ : Rep (N := M * p) (Lc ι) (qExpand ℂ (d * p) (jqModC ℂ)) :=
      ⟨k, Adp, Bdp, mem_LForms_of_isIntegral hIA, mem_LForms_of_isIntegral hIB, hQB0, by rw [hx, div_mul_cancel₀ _ hQB0]⟩

    have hκ0 : ((p : ℚ) ^ (-k)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (NeZero.ne p))
    have mkD : ∀ (F : ModularForm 𝒮ℒ k) (r : PowerSeries ℤ) (Fdp : MF (M * p) k), IsIntegralQExp (⇑F) r →
        (⇑Fdp : ℍ → ℂ) = (fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ)) → IsIntegralQExp (⇑Fdp) (spread (d * p) r) →
        ∃ e : WData p (γW p M hpM) (Lc ι) Fdp, e.D = 1 ∧
          Q e.φ = HahnSeries.C ((((p : ℚ) ^ (-k) : ℚ) : ℂ)) * qExpand ℂ d (intSeriesC ℂ r) := by
      intro F r Fdp hF hFdp hIFdp
      have hWF := Wfun_comp_mul_of_dvd p M hpM d hd F Fdp hFdp
      let d₀ := wdata hW (mem_LForms_of_isIntegral hIFdp)
      have hDc : (d₀.D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr d₀.hD
      have hinv : ((d₀.D : ℂ))⁻¹ ∈ Lc ι := inv_mem (intCast_mem _ d₀.D)
      refine ⟨⟨1, one_ne_zero, (⟨_, hinv⟩ : Lc ι) • d₀.φ, Submodule.smul_mem _ _ d₀.hφ, ?_⟩, rfl, ?_⟩
      · rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, Int.cast_one, one_smul]
        simp [inv_mul_cancel₀ hDc]
      · show Q ((⟨_, hinv⟩ : Lc ι) • d₀.φ) = _
        have hcoe : (⇑((⟨_, hinv⟩ : Lc ι) • d₀.φ) : ℍ → ℂ) =
            ((((p : ℚ) ^ (-k) : ℚ) : ℂ)) • fun τ => F (ModularForm.heckeDiagMatrix d • τ) := by
          rw [subfield_smul_eq, ModularForm.IsGLPos.coe_smul, d₀.eq, smul_smul, hWF]
          simp [inv_mul_cancel₀ hDc]
        obtain ⟨Fd, hFd⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) d hdMp F
        have hI := isIntegralQExp_comp_heckeDiagMatrix d F hF
        rw [← hFd] at hI hcoe
        have hκL : ((((p : ℚ) ^ (-k) : ℚ) : ℂ)) ∈ Lc ι := ⟨algebraMap ℚ L ((p : ℚ) ^ (-k)), by simp⟩
        have : (⟨_, hinv⟩ : Lc ι) • d₀.φ = (⟨_, hκL⟩ : Lc ι) • Fd := DFunLike.ext' (by
          rw [hcoe, subfield_smul_eq, ModularForm.IsGLPos.coe_smul])
        rw [this, subfield_smul_eq, Q_smul, Q_eq_intSeriesC hI, intSeriesC_spread]
    obtain ⟨dA, hdA, hQdA⟩ := mkD A rA Adp hA hAdp hIA
    obtain ⟨dB, hdB, hQdB⟩ := mkD B rB Bdp hB hBdp hIB
    have hκC : (HahnSeries.C ((((p : ℚ) ^ (-k) : ℚ) : ℂ)) : LaurentSeries ℂ) ≠ 0 :=
      (map_ne_zero HahnSeries.C).mpr (by exact_mod_cast hκ0)
    rw [phiHom_apply hW hmem ρ, phiRep_eq_wval hW ρ dA dB, wval, hdA, hdB, hQdA, hQdB]
    simp only [Int.cast_one, div_one, map_one, one_mul]
    rw [mul_div_mul_left _ _ hκC, hjq, map_div₀]

include hK in

theorem coe_sigmaFun_qExpand (d : ℕ) [NeZero d] (hd : d ∣ M) :
    haveI : NeZero (d * p) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)⟩
    (∀ x : K, (x : LaurentSeries L) = coeffEmb L (qExpand ℚ d jq) →
      ((sigmaFun ι K hK hW x : K) : LaurentSeries L) = coeffEmb L (qExpand ℚ (d * p) jq)) ∧
    (∀ x : K, (x : LaurentSeries L) = coeffEmb L (qExpand ℚ (d * p) jq) →
      ((sigmaFun ι K hK hW x : K) : LaurentSeries L) = coeffEmb L (qExpand ℚ d jq)) := by
  haveI : NeZero (d * p) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)⟩
  obtain ⟨⟨hmem₁, hval₁⟩, ⟨hmem₂, hval₂⟩⟩ := phiHom_qExpand_jqModC ι p M hpM hW d hd
  constructor
  · intro x hx
    apply coeffMap_injective ι
    have hej : emb ι K x = qExpand ℂ d (jqModC ℂ) := by
      rw [emb_apply, hx, coeffMap_coeffEmb, coeffEmb_qExpand, coeffEmb_jq_eq_jqModC]
    rw [← emb_apply, emb_sigmaFun, phiHom_congr ι hW _ hmem₁ hej, hval₁, coeffMap_coeffEmb, coeffEmb_qExpand,
      coeffEmb_jq_eq_jqModC]
  · intro x hx
    apply coeffMap_injective ι
    have hej : emb ι K x = qExpand ℂ (d * p) (jqModC ℂ) := by
      rw [emb_apply, hx, coeffMap_coeffEmb, coeffEmb_qExpand, coeffEmb_jq_eq_jqModC]
    rw [← emb_apply, emb_sigmaFun, phiHom_congr ι hW _ hmem₂ hej, hval₂, coeffMap_coeffEmb, coeffEmb_qExpand,
      coeffEmb_jq_eq_jqModC]

end DegenValue
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

end INVOL
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

namespace TWISTP

p2m_open "ModularCurve~coeffEmb_qExpand~coeffMap_injective" in open INVOL  in
theorem exists_sigma_generators
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,
      (∀ j' : ↥K, ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq →
        ((σ j' : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) ∧
      ∀ (d : ℕ) [NeZero d], d ∣ M →
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq)) ∧
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq)) := by
  let ι := ιC p L
  have hW := wpHyp p M L hpM (γW p M hpM) (γW_mem p M hpM) (γW_dvd p M hpM)
  have hW' := wpHyp p M L hpM (γW' p M hpM) (γW'_mem p M hpM) (γW'_dvd p M hpM)
  have hu : ((pUnit p : ℝˣ) : ℝ) = p := rfl
  have hcomp := Wfun_Wfun_of_mul_eq_scalar (γW p M hpM) (γW' p M hpM) (pUnit p) hu (mul_eq_scalar p M hpM)
  have hcomp' := Wfun_Wfun_of_mul_eq_scalar (γW' p M hpM) (γW p M hpM) (pUnit p) hu (mul_eq_scalar' p M hpM)
  refine ⟨sigma ι K hK hW hW' _ hcomp _ hcomp', fun j' hj' => coe_sigmaFun_j ι K hK hW j' hj', fun d _ hd => ?_⟩
  exact coe_sigmaFun_qExpand ι p M hpM K hK hW d hd

p2m_open "ModularCurve~coeffEmb_qExpand~coeffMap_injective" in open INVOL  in
theorem exists_sigma_generators_W
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,
      (∀ j' : ↥K, ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq →
        ((σ j' : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) ∧
      (∀ (d : ℕ) [NeZero d], d ∣ M →
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq)) ∧
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq))) ∧
      (∃ (ι' : L →+* ℂ) (γ' : SL(2, ℤ)), γ' ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ' 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι' (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι' (c i)) • F i) ∧
            ModularCurve.coeffMap ι' ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) := by
  let ι := ιC p L
  have hW := wpHyp p M L hpM (γW p M hpM) (γW_mem p M hpM) (γW_dvd p M hpM)
  have hW' := wpHyp p M L hpM (γW' p M hpM) (γW'_mem p M hpM) (γW'_dvd p M hpM)
  have hu : ((pUnit p : ℝˣ) : ℝ) = p := rfl
  have hcomp := Wfun_Wfun_of_mul_eq_scalar (γW p M hpM) (γW' p M hpM) (pUnit p) hu (mul_eq_scalar p M hpM)
  have hcomp' := Wfun_Wfun_of_mul_eq_scalar (γW' p M hpM) (γW p M hpM) (pUnit p) hu (mul_eq_scalar' p M hpM)
  refine ⟨sigma ι K hK hW hW' _ hcomp _ hcomp', fun j' hj' => coe_sigmaFun_j ι K hK hW j' hj', fun d _ hd => ?_,
    ι, γW p M hpM, γW_mem p M hpM, γW_dvd p M hpM, fun k f g pf pg hf hg hg0 x hx => ?_⟩
  · exact coe_sigmaFun_qExpand ι p M hpM K hK hW d hd
  · exact generatorLaw ι K hK hW hW' _ hcomp _ hcomp' f g pf pg hf hg hg0 x hx

end TWISTP
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TWISTP

theorem coeffEmb_mem_of_mem_full
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [NeZero p] (f : ↥(ModularCurve.modularFunctionFieldFull (M * p))) :
    ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩
  have hle : ModularCurve.modularFunctionFieldFull (M * p) ≤ ModularCurve.x1FunctionField (M * p) := by
    rw [← ModularCurve.modularFunctionFieldFullC_rat]
    exact (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * p)).trans
      (ModularCurve.qExpFunctionFieldC_mono ℚ (CongruenceSubgroup.Gamma1_in_Gamma0 (M * p)))
  rw [hK]
  exact ModularCurve.coeffEmb_mem_laurentBaseChange L (hle f.2)

theorem clause4_of_generators
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [NeZero p] (σ : ↥K ≃ₐ[L] ↥K)
    (hσ : ∀ (d : ℕ) [NeZero d], d ∣ M →
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq)) ∧
        (∀ x : ↥K, ((x : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (d * p) ModularCurve.jq) →
          ((σ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq))) :
    ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p))) (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
      ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
        ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f : ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ) := by
  classical
  have hp : p.Prime := Fact.out
  have hKmem := coeffEmb_mem_of_mem_full p M L K hK

  have hw : ModularCurve.IsAtkinLehnerAutFull M p (ModularCurve.atkinLehnerInvolutionFull M p) :=
    ModularCurve.isAtkinLehnerAutFull_atkinLehnerInvolutionFull M p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd M p hp hpM)

  let θ : ↥(ModularCurve.modularFunctionFieldFull (M * p)) →+* ↥K :=
    RingHom.codRestrict ((ModularCurve.coeffEmb L).comp (ModularCurve.modularFunctionFieldFull (M * p)).toSubring.subtype) K hKmem
  let ψ₁ : ↥(ModularCurve.modularFunctionFieldFull (M * p)) →+* LaurentSeries L := K.toSubring.subtype.comp ((σ : ↥K →+* ↥K).comp θ)
  let ψ₂ : ↥(ModularCurve.modularFunctionFieldFull (M * p)) →+* LaurentSeries L :=
    ((ModularCurve.coeffEmb L).comp (ModularCurve.modularFunctionFieldFull (M * p)).toSubring.subtype).comp
      (ModularCurve.atkinLehnerInvolutionFull M p : ↥(ModularCurve.modularFunctionFieldFull (M * p)) →+* ↥(ModularCurve.modularFunctionFieldFull (M * p)))
  have hψ₁ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (M * p)), ψ₁ f = ((σ (θ f) : ↥K) : LaurentSeries L) := fun _ => rfl
  have hψ₂ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (M * p)), ψ₂ f =
      ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f : ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ) := fun _ => rfl
  have hθ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (M * p)), ((θ f : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (f : LaurentSeries ℚ) := fun _ => rfl

  suffices H : ∀ x, x ∈ IntermediateField.adjoin ℚ (ModularCurve.divisorExpansions (M * p)) →
      ∀ hx : x ∈ ModularCurve.modularFunctionFieldFull (M * p), ψ₁ ⟨x, hx⟩ = ψ₂ ⟨x, hx⟩ by
    intro f hfK
    have e : (⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) = θ f := Subtype.ext rfl
    rw [e]
    exact (hψ₁ f).symm.trans ((H f f.2 f.2).trans (hψ₂ f))
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hxS =>
    intro hxF
    obtain ⟨e, hne, heMp, rfl⟩ := hxS
    by_cases hpe : p ∣ e
    ·
      obtain ⟨d, rfl⟩ := hpe
      haveI : NeZero d := ⟨fun h => (NeZero.ne (p * d)) (by rw [h, Nat.mul_zero])⟩
      have hdM : d ∣ M := Nat.dvd_of_mul_dvd_mul_left hp.pos (by rwa [Nat.mul_comm M p] at heMp)
      have e1 : (⟨ModularCurve.qExpand ℚ (p * d) ModularCurve.jq, hxF⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p))) =
          ⟨ModularCurve.qExpand ℚ (d * p) ModularCurve.jq,
            ModularCurve.jqd_mem_full (M * p) (Nat.mul_dvd_mul_right hdM p)⟩ :=
        Subtype.ext (ModularCurve.qExpand_congr (Nat.mul_comm p d) _)
      rw [e1, hψ₁, hψ₂, (hw d inferInstance hdM).2]
      exact (hσ d hdM).2 _ (hθ _)
    ·
      haveI : NeZero e := hne
      have heM : e ∣ M :=
        Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe).symm heMp
      rw [hψ₁, hψ₂, (hw e inferInstance heM).1]
      exact (hσ e heM).1 _ (hθ _)
  | algebraMap r =>
    intro hxF
    have ey : (⟨algebraMap ℚ (LaurentSeries ℚ) r, hxF⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p))) = ((r : ℚ) : ↥(ModularCurve.modularFunctionFieldFull (M * p))) := by
      apply Subtype.ext
      show algebraMap ℚ (LaurentSeries ℚ) r = (((r : ℚ) : ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)
      rw [eq_ratCast, SubfieldClass.coe_ratCast]
    rw [ey, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    intro h
    rw [show (⟨x + y, h⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p))) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, ihx hx, ihy hy]
  | inv x hx ihx =>
    intro h
    rw [show (⟨x⁻¹, h⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p))) = (⟨x, hx⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p)))⁻¹ from rfl, map_inv₀, map_inv₀, ihx hx]
  | mul x y hx hy ihx ihy =>
    intro h
    rw [show (⟨x * y, h⟩ : ↥(ModularCurve.modularFunctionFieldFull (M * p))) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, map_mul, ihx hx, ihy hy]

end TWISTP
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul.INVOL"

open scoped MatrixGroups ModularForm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,

      ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧

      (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f :
            ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) ∧

      (∃ (ι : L →+* ℂ) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) := by
  obtain ⟨σ, h1, hgen, hWlaw⟩ := TWISTP.exists_sigma_generators_W p M hpM L K hK
  exact ⟨σ, h1 j hj, TWISTP.clause4_of_generators p M hpM L K hK σ hgen, hWlaw⟩

#print axioms solution

end S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_generatorLaw_x1_mul (solution)
