-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8c771431-9f96-5b33-aa1c-7e4b0f6ba7e3

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold ModularForm Pointwise ComplexConjugate

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf coeffMap coeffMap_coeff coeffMap_single coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff ofPowerSeries_coeff_of_neg IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem realizeOf_eq_div"
namespace ConjPlaceTransport
p2m_open "ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL {k : ℤ} (f : ModularForm Γ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

structure Pres (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm Γ k
  h : ModularForm Γ k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

variable [hT : Fact (ModularGroup.T ∈ Γ)]

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have h : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map h

theorem isBoundedUnder_nhdsNE_coe_iff {u : ℍ → ℝ} {τ : ℍ} :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] (τ : ℂ)) (fun z : ℂ => u (ofComplex z)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) u := by
  rw [← map_coe_nhdsNE, Filter.isBoundedUnder_map_iff]
  simp only [Function.comp_def, ofComplex_apply]

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm Γ k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm Γ k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

theorem meromorphicOrderAt_comp_ofComplex_ne_top {k : ℤ}
    (f : ModularForm Γ k) (hf : f ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (analyticAt_comp_ofComplex f τ).meromorphicAt).mpr (eventually_ne_zero_ofComplex f hf τ)

theorem qL_ne_zero {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT.out)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem realize_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  exact ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq (ofComplex z) hz

theorem meromorphicAt_div (x : LaurentSeries ℂ) (P : Pres Γ x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z))
      (τ : ℂ) :=
  (analyticAt_comp_ofComplex P.g τ).meromorphicAt.div (analyticAt_comp_ofComplex P.h τ).meromorphicAt

theorem meromorphicAt_realize {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realizeOf Γ x (ofComplex z)) (τ : ℂ) :=
  (meromorphicAt_div x P τ).congr (realize_eventuallyEq P τ).symm

theorem meromorphicOrderAt_realize_eq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    ∃ m : ℤ, 0 ≤ m ∧
      meromorphicOrderAt (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z)) (τ : ℂ) = m ∧
      meromorphicOrderAt (fun z : ℂ => realizeOf Γ x (ofComplex z)) (τ : ℂ) =
        meromorphicOrderAt (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) + ((-m : ℤ) : WithTop ℤ) := by
  have hh := meromorphicOrderAt_comp_ofComplex_ne_top P.h P.h_ne τ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hh
  have hm0 : 0 ≤ m := by
    have := (analyticAt_comp_ofComplex P.h τ).meromorphicOrderAt_nonneg
    rw [← hm] at this
    exact_mod_cast this
  refine ⟨m, hm0, hm.symm, ?_⟩
  rw [meromorphicOrderAt_congr (realize_eventuallyEq P τ)]
  have hdiv : (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z)) =
      (fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z)) * (fun z : ℂ => (P.h : ℍ → ℂ) (ofComplex z))⁻¹ := by
    ext z; simp [div_eq_mul_inv]
  rw [hdiv, meromorphicOrderAt_mul (analyticAt_comp_ofComplex P.g τ).meromorphicAt
    (analyticAt_comp_ofComplex P.h τ).meromorphicAt.inv, meromorphicOrderAt_inv, ← hm]
  rfl

theorem qL_mul {a b : ℤ} (f : ModularForm Γ a)
    (g : ModularForm Γ b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT.out), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm Γ a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods hT.out), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm Γ 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm Γ 0)) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT.out), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem mul_ne_zero_of_ne_zero {a b : ℤ} (f : ModularForm Γ a)
    (g : ModularForm Γ b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  obtain ⟨w, hw⟩ := ((eventually_ne_zero f hf UpperHalfPlane.I).and
    (eventually_ne_zero g hg UpperHalfPlane.I)).exists
  have := congrArg (fun F : ModularForm Γ (a + b) => (F : ℍ → ℂ) w) hfg
  simp only [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_zero, Pi.zero_apply,
    mul_eq_zero] at this
  exact this.elim hw.1 hw.2

theorem one_ne_zero' : (1 : ModularForm Γ 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm Γ 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

abbrev Pres.mul {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) : Pres Γ (x * y) where
  k := P.k + Q.k
  g := P.g.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

abbrev Pres.add {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) : Pres Γ (x + y) where
  k := P.k + Q.k
  g := P.g.mul Q.h + P.h.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_add, qL_mul, qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

abbrev Pres.const (Γ : Subgroup SL(2, ℤ)) [Fact (ModularGroup.T ∈ Γ)] (c : ℂ) : Pres Γ (algebraMap ℂ (LaurentSeries ℂ) c) where
  k := 0
  g := c • (1 : ModularForm Γ 0)
  h := 1
  h_ne := one_ne_zero'
  eq := by
    rw [qL_one, mul_one, qL_const]

theorem realize_mul_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (x * y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realizeOf Γ x (ofComplex z)) * fun z : ℂ => realizeOf Γ y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.mul Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ] with z h1 h2 h3
  rw [Pi.mul_apply, h2, h3, h1]
  rw [ModularForm.coe_mul, ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]

theorem realize_add_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres Γ x) (Q : Pres Γ y) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (x + y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realizeOf Γ x (ofComplex z)) + fun z : ℂ => realizeOf Γ y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.add Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ, eventually_ne_zero_ofComplex P.h P.h_ne τ,
    eventually_ne_zero_ofComplex Q.h Q.h_ne τ] with z h1 h2 h3 hP hQ
  rw [Pi.add_apply, h2, h3, h1]
  rw [ModularForm.coe_add, Pi.add_apply, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, div_add_div _ _ hP hQ,
    mul_comm ((P.h : ℍ → ℂ) (ofComplex z)) ((Q.g : ℍ → ℂ) (ofComplex z))]

theorem realize_const_eventuallyEq (c : ℂ) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun _ => c := by
  filter_upwards [realize_eventuallyEq (Pres.const Γ c) τ] with z h1
  rw [h1, ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one]
  simp

theorem realize_smul_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x)
    (γ : Γ) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x ((((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realizeOf Γ x (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  have hsm : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • ofComplex z = (γ : SL(2, ℤ)) • ofComplex z := by
    simp
  have hh : (P.h : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ P.k * (P.h : ℍ → ℂ) (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' P.h γ.2 _
  have hg : (P.g : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ P.k * (P.g : ℍ → ℂ) (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' P.g γ.2 _
  have hd : (denom (γ : SL(2, ℤ)) (ofComplex z) : ℂ) ^ P.k ≠ 0 :=
    zpow_ne_zero _ (denom_ne_zero _ _)
  have hne : (P.h : ℍ → ℂ) ((γ : SL(2, ℤ)) • ofComplex z) ≠ 0 := by
    rw [hh]; exact mul_ne_zero hd hz
  rw [hsm, ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq _ hne,
    ModularCurve.realizeOf_eq_div Γ hT.out P.g P.h x P.eq _ hz, hg, hh, mul_div_mul_left _ _ hd]

section Presented

abbrev CF (Γ : Subgroup SL(2, ℤ)) : Type :=
  ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ))

def pres (x : CF Γ) : Pres Γ (x : LaurentSeries ℂ) :=
  let E := ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem Γ hT.out
    (x : LaurentSeries ℂ) x.2
  ⟨E.choose, E.choose_spec.choose, E.choose_spec.choose_spec.choose,
    E.choose_spec.choose_spec.choose_spec.1, E.choose_spec.choose_spec.choose_spec.2⟩

def Pres.inv {x : LaurentSeries ℂ} (P : Pres Γ x) (hx : x ≠ 0) : Pres Γ x⁻¹ where
  k := P.k
  g := P.h
  h := P.g
  h_ne := by
    intro hg0
    have heq := P.eq
    rw [hg0, show qL (0 : ModularForm Γ P.k) = 0 by simp [qL, UpperHalfPlane.qExpansion_zero]] at heq
    exact (mul_ne_zero hx (qL_ne_zero P.h P.h_ne)) heq
  eq := by
    rw [← P.eq, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx, mul_one]

theorem realize_inv_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x⁻¹ (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (realizeOf Γ x (ofComplex z))⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
    filter_upwards [realize_const_eventuallyEq (Γ := Γ) 0 τ] with z hz
    rw [map_zero] at hz
    rw [hz, inv_zero]
  · filter_upwards [realize_eventuallyEq (P.inv hx) τ, realize_eventuallyEq P τ] with z h1 h2
    rw [h1, h2, inv_div]
    rfl

theorem realize_neg_eventuallyEq {x : LaurentSeries ℂ} (P : Pres Γ x) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ (-x) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => -realizeOf Γ x (ofComplex z) := by
  have hneg : -x = algebraMap ℂ (LaurentSeries ℂ) (-1) * x := by rw [map_neg, map_one]; ring
  rw [hneg]
  filter_upwards [realize_mul_eventuallyEq (Pres.const Γ (-1)) P τ,
    realize_const_eventuallyEq (Γ := Γ) (-1) τ] with z h1 h2
  rw [h1, Pi.mul_apply, h2]
  ring

end Presented

section IntegralReal

theorem qParam_J_smul (τ : ℍ) :
    Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ) = conj (Function.Periodic.qParam 1 (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_J_smul, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_conj]
  congr 1
  simp only [Complex.ofReal_one, div_one, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

variable {Γ : Subgroup SL(2, ℤ)} [hT : Fact (ModularGroup.T ∈ Γ)]

theorem conj_apply_J_smul_of_isIntegralQExp {k : ℤ} (f : ModularForm Γ k) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) (τ : ℍ) : conj (f (J • τ)) = f τ := by
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := one_mem_strictPeriods hT.out
  have hper : Function.Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex f h1
  haveI : Fact (IsCusp OnePoint.infty (Γ : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨(Γ : Subgroup (GL (Fin 2) ℝ)).isCusp_of_mem_strictPeriods one_pos h1⟩
  have hsum := fun σ : ℍ =>
    UpperHalfPlane.hasSum_qExpansion one_pos hper (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) σ

  have hcoeff : ∀ m : ℕ, conj ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m) = (qExpansion 1 (⇑f : ℍ → ℂ)).coeff m := by
    intro m
    rw [← hf.coeff m, map_intCast]
  have hJ := (hsum (J • τ)).star
  simp only [smul_eq_mul, star_mul', star_pow] at hJ
  have hJ' : HasSum (fun m : ℕ => (qExpansion 1 (⇑f : ℍ → ℂ)).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (conj (f (J • τ))) := by
    convert hJ using 2 with m
    all_goals try exact starRingEnd_apply _
    rw [show (star ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m) : ℂ) = conj ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m)
        from rfl, hcoeff m,
      show (star (Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ)) : ℂ) = conj (Function.Periodic.qParam 1 ((J • τ : ℍ) : ℂ))
        from rfl, qParam_J_smul, Complex.conj_conj]
  have hτ := hsum τ
  simp only [smul_eq_mul] at hτ
  exact hJ'.unique hτ

end IntegralReal

section Key

variable (Γ : Subgroup SL(2, ℤ)) [hT : Fact (ModularGroup.T ∈ Γ)]

abbrev kappa : AlgebraicCurve.SemilinearAut ℂ (CF Γ) :=
  arithmeticGalois (qExpFunctionFieldC ℚ Γ) complexConjAlgEquiv

theorem coe_kappa_smul (y : CF Γ) :
    ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) = coeffMap (starRingEnd ℂ) (y : LaurentSeries ℂ) := by
  rw [coe_arithmeticGalois_smul]
  exact coeffMap_congr (RingHom.ext fun _ => rfl) _

theorem kappa_smul_algebraMap (c : ℂ) : kappa Γ • algebraMap ℂ (CF Γ) c = algebraMap ℂ (CF Γ) (conj c) := by
  rw [AlgebraicCurve.SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
  rfl

def moebJ : ℍ ≃ₜ ℍ := Homeomorph.smul UpperHalfPlane.J

theorem moebJ_apply (τ : ℍ) : moebJ τ = J • τ := rfl

theorem tendsto_J_smul_nhdsNE (τ : ℍ) :
    Tendsto (fun w : ℍ => J • w) (𝓝[≠] τ) (𝓝[≠] (J • τ)) := by
  have h := moebJ.map_punctured_nhds_eq τ
  rw [moebJ_apply] at h
  have hfun : (fun w : ℍ => J • w) = moebJ := funext fun w => (moebJ_apply w).symm
  rw [hfun, ← h]
  exact Filter.tendsto_map

theorem eventually_J_smul_of_eventually {p : ℍ → Prop} (τ : ℍ)
    (h : ∀ᶠ z in 𝓝[≠] (((J • τ : ℍ)) : ℂ), p (ofComplex z)) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), p (J • ofComplex z) := by
  rw [eventually_nhdsNE_coe_iff] at h
  exact (eventually_nhdsNE_coe_iff (p := fun w => p (J • w))).mpr ((tendsto_J_smul_nhdsNE τ).eventually h)

def Key (y : CF Γ) : Prop :=
  ∀ τ : ℍ, (fun z : ℂ => realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
    fun z : ℂ => conj (realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z))

theorem key_algebraMap (c : ℂ) : Key Γ (algebraMap ℂ (CF Γ) c) := by
  intro τ
  rw [kappa_smul_algebraMap]
  have h1 := realize_const_eventuallyEq (Γ := Γ) (conj c) τ
  have h2 := eventually_J_smul_of_eventually (p := fun w => realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) w = c)
    τ (realize_const_eventuallyEq (Γ := Γ) c (J • τ))
  filter_upwards [h1, h2] with z e1 e2
  show realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) (conj c)) (ofComplex z) =
    conj (realizeOf Γ (algebraMap ℂ (LaurentSeries ℂ) c) (J • ofComplex z))
  rw [e1, e2]

theorem Key.add {x y : CF Γ} (hx : Key Γ x) (hy : Key Γ y) : Key Γ (x + y) := by
  intro τ
  rw [smul_add]
  have h1 := realize_add_eventuallyEq (pres (kappa Γ • x)) (pres (kappa Γ • y)) τ
  have h2 := eventually_J_smul_of_eventually
    (p := fun w => realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) + ((y : CF Γ) : LaurentSeries ℂ)) w =
      realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w + realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w)
    τ (realize_add_eventuallyEq (pres x) (pres y) (J • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ) + ((kappa Γ • y : CF Γ) : LaurentSeries ℂ)) (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) + ((y : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, Pi.add_apply, e3, e4, e2, map_add]

theorem Key.mul {x y : CF Γ} (hx : Key Γ x) (hy : Key Γ y) : Key Γ (x * y) := by
  intro τ
  rw [smul_mul']
  have h1 := realize_mul_eventuallyEq (pres (kappa Γ • x)) (pres (kappa Γ • y)) τ
  have h2 := eventually_J_smul_of_eventually
    (p := fun w => realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) * ((y : CF Γ) : LaurentSeries ℂ)) w =
      realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w * realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w)
    τ (realize_mul_eventuallyEq (pres x) (pres y) (J • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ) * ((kappa Γ • y : CF Γ) : LaurentSeries ℂ)) (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ) * ((y : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, Pi.mul_apply, e3, e4, e2, map_mul]

theorem Key.neg {x : CF Γ} (hx : Key Γ x) : Key Γ (-x) := by
  intro τ
  rw [smul_neg]
  have h1 := realize_neg_eventuallyEq (pres (kappa Γ • x)) τ
  have h2 := eventually_J_smul_of_eventually
    (p := fun w => realizeOf Γ (-((x : CF Γ) : LaurentSeries ℂ)) w = -realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w)
    τ (realize_neg_eventuallyEq (pres x) (J • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf Γ (-((kappa Γ • x : CF Γ) : LaurentSeries ℂ)) (ofComplex z) =
    conj (realizeOf Γ (-((x : CF Γ) : LaurentSeries ℂ)) (J • ofComplex z))
  rw [e1, e3, e2, map_neg]

theorem Key.inv {x : CF Γ} (hx : Key Γ x) : Key Γ x⁻¹ := by
  intro τ
  rw [smul_inv'']
  have h1 := realize_inv_eventuallyEq (pres (kappa Γ • x)) τ
  have h2 := eventually_J_smul_of_eventually
    (p := fun w => realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ)⁻¹ w = (realizeOf Γ ((x : CF Γ) : LaurentSeries ℂ) w)⁻¹)
    τ (realize_inv_eventuallyEq (pres x) (J • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf Γ (((kappa Γ • x : CF Γ) : LaurentSeries ℂ)⁻¹) (ofComplex z) =
    conj (realizeOf Γ (((x : CF Γ) : LaurentSeries ℂ)⁻¹) (J • ofComplex z))
  rw [e1, e3, e2, map_inv₀]

theorem coeffEmb_intSeriesC_eq_qL {k : ℤ} {f : ModularForm Γ k} {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) : coeffEmb ℂ (intSeriesC ℚ p) = qL f := by
  have h1 : coeffEmb ℂ (intSeriesC ℚ p) = intSeriesC ℂ p := by
    ext n
    rw [coeffEmb_coeff]
    rcases lt_or_ge n 0 with hn | hn
    · rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn,
        map_zero]
    · lift n to ℕ using hn with n
      rw [intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast,
        eq_intCast, map_intCast]
  rw [h1, intSeriesC, hf]

theorem coeffMap_conj_coeffEmb (w : LaurentSeries ℚ) : coeffMap (starRingEnd ℂ) (coeffEmb ℂ w) = coeffEmb ℂ w := by
  ext n
  rw [coeffMap_coeff, coeffEmb_coeff]
  exact map_ratCast (starRingEnd ℂ) (w.coeff n)

theorem key_generator {k : ℤ} (f g : ModularForm Γ k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    Key Γ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ := by
  intro τ
  have hgq : qL g ≠ 0 := by
    rw [← coeffEmb_intSeriesC_eq_qL Γ hg]
    intro h0
    apply hg0
    exact (coeffEmb ℂ).injective (h0.trans (map_zero _).symm)
  have hgne : g ≠ 0 := by
    intro h; apply hgq; simp [qL, h, UpperHalfPlane.qExpansion_zero]
  set y : CF Γ := ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hydef

  have hκy : (kappa Γ • y : CF Γ) = y := by
    apply Subtype.ext
    rw [coe_kappa_smul]
    exact coeffMap_conj_coeffEmb _

  have hy : ((y : CF Γ) : LaurentSeries ℂ) * qL g = qL f := by
    show coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg) * qL g = qL f
    rw [map_div₀, coeffEmb_intSeriesC_eq_qL Γ hf, coeffEmb_intSeriesC_eq_qL Γ hg, div_mul_cancel₀ _ hgq]
  let Py : Pres Γ ((y : CF Γ) : LaurentSeries ℂ) := ⟨k, f, g, hgne, hy⟩
  rw [hκy]
  have h1 := realize_eventuallyEq Py τ
  have h2 := eventually_J_smul_of_eventually
    (p := fun w => realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w = (f : ℍ → ℂ) w / (g : ℍ → ℂ) w) τ
    (by
      filter_upwards [realize_eventuallyEq Py (J • τ)] with z hz
      exact hz)
  filter_upwards [h1, h2] with z e1 e2
  rw [e1, e2, map_div₀, conj_apply_J_smul_of_isIntegralQExp f hf, conj_apply_J_smul_of_isIntegralQExp g hg]

theorem key_all (y : CF Γ) : Key Γ y := by
  obtain ⟨x, hx⟩ := y
  have inner : ∀ (w : LaurentSeries ℚ) (hw : w ∈ qExpFunctionFieldC ℚ Γ),
      Key Γ ⟨coeffEmb ℂ w, coeffEmb_mem_laurentBaseChange ℂ hw⟩ := by
    intro w hw
    have hw' : w ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) := hw
    induction hw' using Subfield.closure_induction with
    | mem z hz =>
        rcases hz with ⟨r, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
        · have : (⟨coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
              algebraMap ℂ (CF Γ) (r : ℂ) := by
            apply Subtype.ext
            show coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ)
            rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
            simp
          rw [this]
          exact key_algebraMap Γ (r : ℂ)
        · exact key_generator Γ f g pf pg hf hg hg0
    | one =>
        have : (⟨coeffEmb ℂ 1, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) = algebraMap ℂ (CF Γ) 1 :=
          Subtype.ext (by simp)
        rw [this]; exact key_algebraMap Γ 1
    | add a b ha hb iha ihb =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have hmem_b : b ∈ qExpFunctionFieldC ℚ Γ := hb
        have : (⟨coeffEmb ℂ (a + b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) +
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a + b) = coeffEmb ℂ a + coeffEmb ℂ b; rw [map_add]
        rw [this]; exact (iha hmem_a).add Γ (ihb hmem_b)
    | neg a ha iha =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have : (⟨coeffEmb ℂ (-a), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            -(⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) := by
          apply Subtype.ext; show coeffEmb ℂ (-a) = -coeffEmb ℂ a; rw [map_neg]
        rw [this]; exact (iha hmem_a).neg Γ
    | inv a ha iha =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have : (⟨coeffEmb ℂ a⁻¹, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ)⁻¹ := by
          apply Subtype.ext; show coeffEmb ℂ a⁻¹ = (coeffEmb ℂ a)⁻¹; rw [map_inv₀]
        rw [this]; exact (iha hmem_a).inv Γ
    | mul a b ha hb iha ihb =>
        have hmem_a : a ∈ qExpFunctionFieldC ℚ Γ := ha
        have hmem_b : b ∈ qExpFunctionFieldC ℚ Γ := hb
        have : (⟨coeffEmb ℂ (a * b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : CF Γ) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : CF Γ) *
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a * b) = coeffEmb ℂ a * coeffEmb ℂ b; rw [map_mul]
        rw [this]; exact (iha hmem_a).mul Γ (ihb hmem_b)
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℂ (LaurentSeries ℂ)) ∪
      (coeffEmb ℂ) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) := (mem_laurentBaseChange_iff).mp hx
  induction hx' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨w, hw, rfl⟩
      · have : (⟨algebraMap ℂ (LaurentSeries ℂ) c, hx⟩ : CF Γ) = algebraMap ℂ (CF Γ) c := Subtype.ext rfl
        rw [this]; exact key_algebraMap Γ c
      · exact inner w hw
  | one =>
      have : (⟨1, hx⟩ : CF Γ) = algebraMap ℂ (CF Γ) 1 := Subtype.ext (by simp)
      rw [this]; exact key_algebraMap Γ 1
  | add a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a + b, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ) + ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).add Γ (ihb hmb)
  | neg a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨-a, hx⟩ : CF Γ) = -(⟨a, hma⟩ : CF Γ) := Subtype.ext rfl
      rw [this]; exact (iha hma).neg Γ
  | inv a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨a⁻¹, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ)⁻¹ := Subtype.ext rfl
      rw [this]; exact (iha hma).inv Γ
  | mul a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a * b, hx⟩ : CF Γ) = (⟨a, hma⟩ : CF Γ) * ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).mul Γ (ihb hmb)

end Key

section Place

variable (Γ : Subgroup SL(2, ℤ)) [hT : Fact (ModularGroup.T ∈ Γ)]

theorem isBoundedUnder_comp_J_smul_iff (u : ℍ → ℝ) (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun w : ℍ => u (J • w)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] (J • τ)) u := by
  have h := moebJ.map_punctured_nhds_eq τ
  rw [moebJ_apply] at h
  have hfun : (fun w : ℍ => u (J • w)) = u ∘ moebJ := funext fun w => by rw [Function.comp_apply, moebJ_apply]
  rw [hfun, ← Filter.isBoundedUnder_map_iff, h]

theorem mem_smul_place_iff (g : AlgebraicCurve.SemilinearAut ℂ (CF Γ)) (v : AlgebraicCurve.Place ℂ (CF Γ)) (x : CF Γ) :
    x ∈ (g • v).toValuationSubring ↔ g⁻¹ • x ∈ v.toValuationSubring := by
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem isBoundedUnder_congr_of_eventuallyEq {α β : Type*} {r : β → β → Prop} {l : Filter α}
    {u v : α → β} (h : u =ᶠ[l] v) : IsBoundedUnder r l u ↔ IsBoundedUnder r l v := by
  show (Filter.map u l).IsBounded r ↔ (Filter.map v l).IsBounded r
  rw [Filter.map_congr h]

theorem J_smul_J_smul (τ : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • τ = τ := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

theorem kappa_mul_kappa : kappa Γ * kappa Γ = 1 := by
  rw [kappa, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

theorem kappa_inv : (kappa Γ)⁻¹ = kappa Γ :=
  inv_eq_of_mul_eq_one_right (kappa_mul_kappa Γ)

theorem smul_pt_eq (D : ComplexPlaceDictionaryOf Γ (qExpFunctionFieldC ℚ Γ))
    (hkey : ∀ y : CF Γ, Key Γ y) (τ : ℍ) :
    kappa Γ • D.pt τ = D.pt (J • τ) := by

  suffices h : D.pt (J • τ) = kappa Γ • D.pt τ from h.symm
  apply AlgebraicCurve.Place.ext
  ext y
  rw [mem_smul_place_iff, kappa_inv, D.mem_pt_iff, D.mem_pt_iff]
  have hk := hkey y τ
  have hk' : (fun z : ℂ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)‖) =ᶠ[𝓝[≠] ((τ : ℍ) : ℂ)]
      fun z : ℂ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z)‖ := by
    filter_upwards [hk] with z hz
    rw [hz, Complex.norm_conj]
  calc IsBoundedUnder (· ≤ ·) (𝓝[≠] (J • τ)) (fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) w‖)
      ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • w)‖) :=
        (isBoundedUnder_comp_J_smul_iff _ _).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] ((τ : ℍ) : ℂ))
          (fun z : ℂ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • ofComplex z)‖) :=
        (isBoundedUnder_nhdsNE_coe_iff
          (u := fun w : ℍ => ‖realizeOf Γ ((y : CF Γ) : LaurentSeries ℂ) (J • w)‖)).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] ((τ : ℍ) : ℂ))
          (fun z : ℂ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) (ofComplex z)‖) :=
        (isBoundedUnder_congr_of_eventuallyEq hk').symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun w : ℍ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) w‖) :=
        isBoundedUnder_nhdsNE_coe_iff (u := fun w : ℍ => ‖realizeOf Γ ((kappa Γ • y : CF Γ) : LaurentSeries ℂ) w‖)

end Place

end ModularCurve.ConjPlaceTransport
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve.ConjPlaceTransport"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve.ConjPlaceTransport"

open scoped MatrixGroups in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.ModularCurve ModularCurve.ConjPlaceTransport in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    ModularCurve.arithmeticGalois F₀ complexConjAlgEquiv • D.pt τ = D.pt (UpperHalfPlane.J • τ) := by
  subst hF
  haveI : Fact (ModularGroup.T ∈ Γ) := ⟨hT⟩
  exact smul_pt_eq Γ D (key_all Γ) τ

end S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt (solution)
