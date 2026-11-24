-- Prove2me | solution 1 for GlobalTheory.VolFin.lineBundle_global_sections_functionField_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:54.874495+00:00
-- url     : https://prove2.me/submissions/53a7d873-f38a-4bbd-8b05-eab94a4cace8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_gen_rs
import Theorems.Thm_GlobalTheory_VolFin_eq_of_gen
import Theorems.Thm_GlobalTheory_VolFin_tr_self
import Theorems.Thm_GlobalTheory_VolFin_gen_sec
import Theorems.Thm_GlobalTheory_VolFin_gen_constFn
import Theorems.Thm_GlobalTheory_VolFin_exists_sec
import Theorems.Thm_GlobalTheory_ZV_MapDeg_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (V : Submodule K X.functionField)
    (hV : ∀ f, f ∈ V ↔ ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) (r : ℕ) :
    SectionsHaveFiniteDimension p N r ↔ Module.Finite K V ∧ Module.finrank K V = r := by
  let θ : N.Sec → V := fun s => ⟨gen _ h₀ (s.f j₀), (hV _).2 fun i =>
    ⟨rs X (hW i) (s.f (c i)), by rw [gen_rs, gen_sec s (c i) j₀ _ h₀, _root_.mul_comm]⟩⟩
  have hθ : Function.Surjective θ := fun f => by
    obtain ⟨s, hs⟩ := exists_sec hN j₀ h₀ W c hW hη hc f ((hV f).1 f.2)
    exact ⟨s, Subtype.ext hs⟩
  have key : ∀ (s : Fin r → N.Sec) (t : N.Sec) (a : Fin r → K),
      (∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j) ↔ ∑ i, a i • θ (s i) = θ t := by
    intro s t a
    have e : ∀ j hj, gen _ hj (∑ i, constFn p _ (a i) * (s i).f j) =
        tr N j j₀ hj h₀ * ((∑ i, a i • θ (s i) : V) : X.functionField) := by
      intro j hj
      rw [map_sum, AddSubmonoidClass.coe_finset_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, gen_constFn, ← halg, gen_sec (s i) j j₀ hj h₀, SetLike.val_smul, Algebra.smul_def]
      ring
    constructor
    · intro h
      apply Subtype.ext
      have := e j₀ h₀
      rw [tr_self hN, _root_.one_mul, ← h j₀] at this
      exact this.symm
    · intro h j
      refine eq_of_gen fun hj => ?_
      rw [e, h, gen_sec t j j₀ hj h₀]
  constructor
  · rintro ⟨s, hs⟩
    have hb : Function.Bijective (Fintype.linearCombination K fun i => θ (s i)) := by
      rw [Function.bijective_iff_existsUnique]
      intro f
      obtain ⟨t, rfl⟩ := hθ f
      simpa only [key, Fintype.linearCombination_apply] using hs t
    have E := LinearEquiv.ofBijective _ hb
    exact ⟨Module.Finite.equiv E, by rw [← E.finrank_eq, Module.finrank_fin_fun]⟩
  · rintro ⟨hf, hr⟩
    let b := Module.finBasisOfFinrankEq K V hr
    choose s hs using fun i => hθ (b i)
    refine ⟨s, fun t => ?_⟩
    simp only [key, hs]
    refine ⟨b.equivFun (θ t), b.sum_equivFun _, fun a ha => ?_⟩
    rw [← ha, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
end GlobalTheory.VolFin
