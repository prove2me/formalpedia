-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/886f6207-d57b-5b2a-8d16-ab659a53b5b0

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff ofPowerSeries_coeff_of_neg translation_mem_GammaH xHFunctionField restrictForm IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem realizeOf_eq_div"
namespace DiamondPlaceTransport
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

section SlashForm

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}

theorem gammaH_le_conj (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hA
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * a * γ⁻¹, ?_, ?_⟩
  · exact CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨a, ha⟩
  · rw [map_mul, map_mul, map_inv]
    rfl

def slashForm (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H) k) : ModularForm (CohCarrier.GammaH M H) k :=
  restrictForm (gammaH_le_conj γ hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

theorem slashForm_apply (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H) k) (τ : ℍ) :
    slashForm γ hγ f τ = f (γ • τ) * (denom γ τ) ^ (-k) := by
  rw [show slashForm γ hγ f τ = ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) τ from rfl,
    ← ModularForm.SL_slash, ModularForm.SL_slash_apply]

theorem slashForm_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (f : ModularForm (CohCarrier.GammaH M H) k) (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h0
  apply hf
  have hfun : (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_slashForm γ hγ f, h0]; rfl
  have : (⇑f : ℍ → ℂ) = 0 := by
    have h2 := congrArg (fun F : ℍ → ℂ => F ∣[k] ((γ : GL (Fin 2) ℝ))⁻¹) hfun
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using h2
  exact DFunLike.coe_injective (this.trans ModularForm.coe_zero.symm)

end SlashForm

def IsPullbackAlong (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (σ : ↥(laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ] ↥(laurentBaseChange ℂ (xHFunctionField M H)))
    (γ : SL(2, ℤ)) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0),
    ((σ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        ↥(laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) *
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

section Key

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

scoped instance factT : Fact (ModularGroup.T ∈ CohCarrier.GammaH M H) := ⟨translation_mem_GammaH M H⟩

def moeb (γ : SL(2, ℤ)) : ℍ ≃ₜ ℍ := Homeomorph.smul ((γ : GL (Fin 2) ℝ))

omit [NeZero M] in
theorem moeb_apply (γ : SL(2, ℤ)) (τ : ℍ) : moeb γ τ = γ • τ := by
  show ((γ : GL (Fin 2) ℝ)) • τ = γ • τ
  simp

omit [NeZero M] in

theorem tendsto_smul_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun w : ℍ => γ • w) (𝓝[≠] τ) (𝓝[≠] (γ • τ)) := by
  have h := (moeb γ).map_punctured_nhds_eq τ
  rw [moeb_apply] at h
  have hfun : (fun w : ℍ => γ • w) = moeb γ := funext fun w => (moeb_apply γ w).symm
  rw [hfun, ← h]
  exact Filter.tendsto_map

omit [NeZero M] in

theorem eventually_smul_of_eventually {p : ℍ → Prop} (γ : SL(2, ℤ)) (τ : ℍ)
    (h : ∀ᶠ z in 𝓝[≠] (((γ • τ : ℍ)) : ℂ), p (ofComplex z)) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), p (γ • ofComplex z) := by
  rw [eventually_nhdsNE_coe_iff] at h
  exact (eventually_nhdsNE_coe_iff (p := fun w => p (γ • w))).mpr ((tendsto_smul_nhdsNE γ τ).eventually h)

def Key (σ : (laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ] (laurentBaseChange ℂ (xHFunctionField M H))) (γ : SL(2, ℤ)) (y : (laurentBaseChange ℂ (xHFunctionField M H))) : Prop :=
  ∀ τ : ℍ, (fun z : ℂ => realizeOf (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
    fun z : ℂ => realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)

variable (σ : (laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ] (laurentBaseChange ℂ (xHFunctionField M H))) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)

theorem key_algebraMap (c : ℂ) : Key σ γ (algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) c) := by
  intro τ
  rw [AlgEquiv.commutes]
  have h1 := realize_const_eventuallyEq (Γ := CohCarrier.GammaH M H) c τ
  have h2 := eventually_smul_of_eventually (p := fun w => realizeOf (CohCarrier.GammaH M H) (algebraMap ℂ (LaurentSeries ℂ) c) w = c)
    γ τ (realize_const_eventuallyEq (Γ := CohCarrier.GammaH M H) c (γ • τ))
  filter_upwards [h1, h2] with z e1 e2
  exact e1.trans e2.symm

theorem Key.add {x y : (laurentBaseChange ℂ (xHFunctionField M H))} (hx : Key σ γ x) (hy : Key σ γ y) : Key σ γ (x + y) := by
  intro τ
  rw [map_add]
  have h1 := realize_add_eventuallyEq (pres (σ x)) (pres (σ y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H) (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) + ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w =
      realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w + realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    γ τ (realize_add_eventuallyEq (pres x) (pres y) (γ • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf (CohCarrier.GammaH M H) (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) + ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H) (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) + ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, Pi.add_apply, e3, e4, e2]

theorem Key.mul {x y : (laurentBaseChange ℂ (xHFunctionField M H))} (hx : Key σ γ x) (hy : Key σ γ y) : Key σ γ (x * y) := by
  intro τ
  rw [map_mul]
  have h1 := realize_mul_eventuallyEq (pres (σ x)) (pres (σ y)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H) (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w =
      realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w * realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    γ τ (realize_mul_eventuallyEq (pres x) (pres y) (γ • τ))
  filter_upwards [h1, h2, hx τ, hy τ] with z e1 e2 e3 e4
  show realizeOf (CohCarrier.GammaH M H) (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H) (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, Pi.mul_apply, e3, e4, e2]

theorem Key.neg {x : (laurentBaseChange ℂ (xHFunctionField M H))} (hx : Key σ γ x) : Key σ γ (-x) := by
  intro τ
  rw [map_neg]
  have h1 := realize_neg_eventuallyEq (pres (σ x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H) (-((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) w = -realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)
    γ τ (realize_neg_eventuallyEq (pres x) (γ • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf (CohCarrier.GammaH M H) (-((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H) (-((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)) (γ • ofComplex z)
  rw [e1, e3, e2]

theorem Key.inv {x : (laurentBaseChange ℂ (xHFunctionField M H))} (hx : Key σ γ x) : Key σ γ x⁻¹ := by
  intro τ
  rw [map_inv₀]
  have h1 := realize_inv_eventuallyEq (pres (σ x)) τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹ w = (realizeOf (CohCarrier.GammaH M H) ((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w)⁻¹)
    γ τ (realize_inv_eventuallyEq (pres x) (γ • τ))
  filter_upwards [h1, h2, hx τ] with z e1 e2 e3
  show realizeOf (CohCarrier.GammaH M H) (((σ x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹) (ofComplex z) =
    realizeOf (CohCarrier.GammaH M H) (((x : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ)⁻¹) (γ • ofComplex z)
  rw [e1, e3, e2]

theorem coeffEmb_intSeriesC_eq_qL {k : ℤ} {f : ModularForm (CohCarrier.GammaH M H) k} {p : PowerSeries ℤ}
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

include hγ in

theorem key_generator
    (hσ : IsPullbackAlong M H σ γ)
    {k : ℤ} (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    Key σ γ ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ := by
  intro τ

  have hgq : qL g ≠ 0 := by
    rw [← coeffEmb_intSeriesC_eq_qL hg]
    intro h0
    apply hg0
    have hinj : Function.Injective (coeffEmb ℂ : LaurentSeries ℚ → LaurentSeries ℂ) := (coeffEmb ℂ).injective
    exact hinj (h0.trans (map_zero _).symm)
  have hgne : g ≠ 0 := by
    intro h; apply hgq; simp [qL, h, UpperHalfPlane.qExpansion_zero]

  set y : (laurentBaseChange ℂ (xHFunctionField M H)) := ⟨coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange ℂ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hydef
  have hpres : ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * qL (slashForm γ hγ g) = qL (slashForm γ hγ f) :=
    hσ k f g pf pg hf hg hg0
  let Pσ : Pres (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) :=
    ⟨k, slashForm γ hγ f, slashForm γ hγ g, slashForm_ne_zero γ hγ g hgne, hpres⟩

  have hy : ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) * qL g = qL f := by
    show coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg) * qL g = qL f
    rw [map_div₀, coeffEmb_intSeriesC_eq_qL hf, coeffEmb_intSeriesC_eq_qL hg, div_mul_cancel₀ _ hgq]
  let Py : Pres (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) := ⟨k, f, g, hgne, hy⟩
  have h1 := realize_eventuallyEq Pσ τ
  have h2 := eventually_smul_of_eventually
    (p := fun w => realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w = (f : ℍ → ℂ) w / (g : ℍ → ℂ) w) γ τ
    (by
      filter_upwards [realize_eventuallyEq Py (γ • τ)] with z hz
      exact hz)
  have h3 := eventually_smul_of_eventually (p := fun w => (g : ℍ → ℂ) w ≠ 0) γ τ
    (eventually_ne_zero_ofComplex g hgne (γ • τ))
  filter_upwards [h1, h2, h3] with z e1 e2 e3
  rw [e1, e2]
  show (slashForm γ hγ f : ℍ → ℂ) (ofComplex z) / (slashForm γ hγ g : ℍ → ℂ) (ofComplex z) = _
  rw [slashForm_apply, slashForm_apply,
    mul_div_mul_right _ _ (zpow_ne_zero _ (denom_ne_zero γ (ofComplex z)))]

include hγ in

theorem key_all
    (hσ : IsPullbackAlong M H σ γ)
    (y : (laurentBaseChange ℂ (xHFunctionField M H))) : Key σ γ y := by
  obtain ⟨x, hx⟩ := y

  have inner : ∀ (w : LaurentSeries ℚ) (hw : w ∈ xHFunctionField M H),
      Key σ γ ⟨coeffEmb ℂ w, coeffEmb_mem_laurentBaseChange ℂ hw⟩ := by
    intro w hw
    have hw' : w ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪
        intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hw
    induction hw' using Subfield.closure_induction with
    | mem z hz =>
        rcases hz with ⟨r, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
        · have : (⟨coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
              algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) (r : ℂ) := by
            apply Subtype.ext
            show coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ)
            rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
            simp
          rw [this]
          exact key_algebraMap σ γ (r : ℂ)
        · exact key_generator σ γ hγ hσ f g pf pg hf hg hg0
    | one =>
        have : (⟨coeffEmb ℂ 1, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) 1 := by
          apply Subtype.ext; show coeffEmb ℂ 1 = algebraMap ℂ (LaurentSeries ℂ) 1; rw [map_one, map_one]
        rw [this]; exact key_algebraMap σ γ 1
    | add a b ha hb iha ihb =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have hmem_b : b ∈ xHFunctionField M H := hb
        have : (⟨coeffEmb ℂ (a + b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) +
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a + b) = coeffEmb ℂ a + coeffEmb ℂ b; rw [map_add]
        rw [this]; exact (iha hmem_a).add σ γ (ihb hmem_b)
    | neg a ha iha =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have : (⟨coeffEmb ℂ (-a), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
            -(⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) := by
          apply Subtype.ext; show coeffEmb ℂ (-a) = -coeffEmb ℂ a; rw [map_neg]
        rw [this]; exact (iha hmem_a).neg σ γ
    | inv a ha iha =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have : (⟨coeffEmb ℂ a⁻¹, coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : (laurentBaseChange ℂ (xHFunctionField M H)))⁻¹ := by
          apply Subtype.ext; show coeffEmb ℂ a⁻¹ = (coeffEmb ℂ a)⁻¹; rw [map_inv₀]
        rw [this]; exact (iha hmem_a).inv σ γ
    | mul a b ha hb iha ihb =>
        have hmem_a : a ∈ xHFunctionField M H := ha
        have hmem_b : b ∈ xHFunctionField M H := hb
        have : (⟨coeffEmb ℂ (a * b), coeffEmb_mem_laurentBaseChange ℂ hw⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) =
            (⟨coeffEmb ℂ a, coeffEmb_mem_laurentBaseChange ℂ hmem_a⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) *
              ⟨coeffEmb ℂ b, coeffEmb_mem_laurentBaseChange ℂ hmem_b⟩ := by
          apply Subtype.ext; show coeffEmb ℂ (a * b) = coeffEmb ℂ a * coeffEmb ℂ b; rw [map_mul]
        rw [this]; exact (iha hmem_a).mul σ γ (ihb hmem_b)

  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℂ (LaurentSeries ℂ)) ∪
      (coeffEmb ℂ) '' (xHFunctionField M H : Set (LaurentSeries ℚ))) := (mem_laurentBaseChange_iff).mp hx
  induction hx' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨w, hw, rfl⟩
      · have : (⟨algebraMap ℂ (LaurentSeries ℂ) c, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) c := Subtype.ext rfl
        rw [this]; exact key_algebraMap σ γ c
      · exact inner w hw
  | one =>
      have : (⟨1, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = algebraMap ℂ (laurentBaseChange ℂ (xHFunctionField M H)) 1 := Subtype.ext (by simp)
      rw [this]; exact key_algebraMap σ γ 1
  | add a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a + b, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) + ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).add σ γ (ihb hmb)
  | neg a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨-a, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = -(⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) := Subtype.ext rfl
      rw [this]; exact (iha hma).neg σ γ
  | inv a ha iha =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have : (⟨a⁻¹, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H)))⁻¹ := Subtype.ext rfl
      rw [this]; exact (iha hma).inv σ γ
  | mul a b ha hb iha ihb =>
      have hma : a ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr ha
      have hmb : b ∈ laurentBaseChange ℂ (xHFunctionField M H) := (mem_laurentBaseChange_iff).mpr hb
      have : (⟨a * b, hx⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) = (⟨a, hma⟩ : (laurentBaseChange ℂ (xHFunctionField M H))) * ⟨b, hmb⟩ := Subtype.ext rfl
      rw [this]; exact (iha hma).mul σ γ (ihb hmb)

end Key

section Place

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem isBoundedUnder_comp_smul_iff (γ : SL(2, ℤ)) (u : ℍ → ℝ) (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun w : ℍ => u (γ • w)) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ • τ)) u := by
  have h := (moeb γ).map_punctured_nhds_eq τ
  rw [moeb_apply] at h
  have hfun : (fun w : ℍ => u (γ • w)) = u ∘ (moeb γ) :=
    funext fun w => by rw [Function.comp_apply, moeb_apply]
  rw [hfun, ← Filter.isBoundedUnder_map_iff, h]

theorem mem_smul_place_iff (g : AlgebraicCurve.SemilinearAut ℂ (laurentBaseChange ℂ (xHFunctionField M H))) (v : AlgebraicCurve.Place ℂ (laurentBaseChange ℂ (xHFunctionField M H))) (x : (laurentBaseChange ℂ (xHFunctionField M H))) :
    x ∈ (g • v).toValuationSubring ↔ g⁻¹ • x ∈ v.toValuationSubring := by
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

omit [NeZero M] in

theorem isBoundedUnder_congr_of_eventuallyEq {α β : Type*} {r : β → β → Prop} {l : Filter α}
    {u v : α → β} (h : u =ᶠ[l] v) : IsBoundedUnder r l u ↔ IsBoundedUnder r l v := by
  show (Filter.map u l).IsBounded r ↔ (Filter.map v l).IsBounded r
  rw [Filter.map_congr h]

theorem smul_pt_eq (D : ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (σ : (laurentBaseChange ℂ (xHFunctionField M H)) ≃ₐ[ℂ] (laurentBaseChange ℂ (xHFunctionField M H))) (γ : SL(2, ℤ)) (hkey : ∀ y : (laurentBaseChange ℂ (xHFunctionField M H)), Key σ γ y) (τ : ℍ) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ) := by

  suffices h : D.pt τ = (AlgebraicCurve.SemilinearAut.ofAlgAut σ)⁻¹ • D.pt (γ⁻¹ • τ) by
    rw [h, smul_inv_smul]
  apply AlgebraicCurve.Place.ext
  ext y
  rw [mem_smul_place_iff, inv_inv, D.mem_pt_iff, D.mem_pt_iff]
  have hσy : ((AlgebraicCurve.SemilinearAut.ofAlgAut σ • y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) =
      ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) := rfl
  rw [hσy]

  have hk := hkey y (γ⁻¹ • τ)
  have hk' : (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)‖) =ᶠ[𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ)]
      fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)‖ := by
    filter_upwards [hk] with z hz
    rw [hz]
  calc IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖)
      ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ • (γ⁻¹ • τ)))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖) := by rw [smul_inv_smul]
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ⁻¹ • τ))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • w)‖) :=
        (isBoundedUnder_comp_smul_iff γ _ _).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ))
          (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • ofComplex z)‖) :=
        (isBoundedUnder_nhdsNE_coe_iff
          (u := fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (γ • w)‖)).symm
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (((γ⁻¹ • τ : ℍ)) : ℂ))
          (fun z : ℂ => ‖realizeOf (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) (ofComplex z)‖) :=
        isBoundedUnder_congr_of_eventuallyEq hk'
    _ ↔ IsBoundedUnder (· ≤ ·) (𝓝[≠] (γ⁻¹ • τ))
          (fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖) :=
        isBoundedUnder_nhdsNE_coe_iff (u := fun w : ℍ => ‖realizeOf (CohCarrier.GammaH M H) ((σ y : (laurentBaseChange ℂ (xHFunctionField M H))) : LaurentSeries ℂ) w‖)

end Place

end ModularCurve.DiamondPlaceTransport
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve.DiamondPlaceTransport"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve.DiamondPlaceTransport"

open scoped MatrixGroups ModularForm in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul.ModularCurve ModularCurve.DiamondPlaceTransport in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0),
        ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
              ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))))
    (τ : UpperHalfPlane) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (γ⁻¹ • τ) :=
  smul_pt_eq D σ γ (fun y => key_all σ γ hγ hσ y) τ

end S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul (solution)
