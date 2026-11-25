-- Prove2me | solution 1 for GlobalTheory.Published.principalPolarisationOneSection.zero_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:02.950532+00:00
-- url     : https://prove2.me/submissions/8d8da711-f231-4167-b993-5f2d03db219c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_AbelianLaws_PrincipalPolarisationOneSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.principalPolarisationOneSection
namespace GlobalTheory.Published.principalPolarisationOneSection
theorem _root_.solution (K : Type) [Field K] :
    Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM (Inh.zeroPolAV (Spec (CommRingCat.of K))).A (Inh.zeroPolAV (Spec (CommRingCat.of K))).L 1
        (baseOver (Spec (CommRingCat.of K)))) = 1 := by
  have : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  set S := Spec (CommRingCat.of K)
  set P := Inh.zeroPolAV S with hP
  have hU : ∀ j, (LPow P.A P.L 1 (baseOver S)).U j = ⊤ := fun j =>
    top_unique fun x _ => Set.mem_iInter.2 fun _ => trivial
  have hbij : ∀ j, Function.Bijective
      (liftHom P.A (T := baseOver S) ((LPow P.A P.L 1 (baseOver S)).U j)) := by
    intro j
    rw [hU j]
    have : IsIso (fst (baseOver S) P.A) := by
      change IsIso (fst (baseOver S) (𝟙_ (Over S)))
      rw [← rightUnitor_hom]; infer_instance
    have : IsIso (fst (baseOver S) P.A).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (fst (baseOver S) P.A)))
    have h2 := ConcreteCategory.bijective_of_isIso ((fst (baseOver S) P.A).left.app ⊤)
    have h3 : Function.Bijective (fst (baseOver S) P.A).left.appTop.hom := h2
    simpa [liftHom] using h3
  let one : SecM P.A P.L 1 (baseOver S) := ⟨fun _ => 1, by
    intro i j
    erw [Inh.linComb_triv_g]; simp only [map_one]; exact (_root_.mul_one _).symm⟩
  let j₀ : (LPow P.A P.L 1 (baseOver S)).ι := fun _ => PUnit.unit
  have hj : ∀ j, j = j₀ := fun j => funext fun _ => rfl
  have hsm : ∀ r : Γ((baseOver S).left, ⊤), (r • one).1 j₀ = liftHom P.A _ r := fun r =>
    _root_.mul_one _
  have hb : Function.Bijective (LinearMap.toSpanSingleton Γ((baseOver S).left, ⊤) _ one) := by
    constructor
    · intro r r' e
      apply (hbij j₀).1
      rw [← hsm, ← hsm]
      exact congrArg (fun s : SecM P.A P.L 1 (baseOver S) => s.1 j₀) e
    · intro s
      obtain ⟨r, hr⟩ := (hbij j₀).2 (s.1 j₀)
      refine ⟨r, Subtype.ext (funext fun j => ?_)⟩
      obtain rfl := hj j
      exact (hsm r).trans hr
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
end GlobalTheory.Published.principalPolarisationOneSection
