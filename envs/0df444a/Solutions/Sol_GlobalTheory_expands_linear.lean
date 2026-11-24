-- Prove2me | solution 1 for GlobalTheory.expands_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:24.856032+00:00
-- url     : https://prove2.me/submissions/a1e7d145-cce9-4c21-b8a8-ed59695bc222

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
import Theorems.Thm_GlobalTheory_ExpandsLinear_secScal_comb
import Theorems.Thm_GlobalTheory_ExpandsLinear_fam_sum_f
import Theorems.Thm_GlobalTheory_expandsAt_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ExpandsLinear
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by
  intro R _ _ I _ D A G _ _ _ U k n b F c s hE hs
  choose r hr σ f hσ hf hE using hE
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun i => c i / algebraMap R (FractionRing R) (r i))
  choose a ha using hd
  have hc : ∀ i, algebraMap R (FractionRing R) (a i) * algebraMap R (FractionRing R) (r i) =
      algebraMap R (FractionRing R) d * c i := fun i => by
    have h0 : algebraMap R (FractionRing R) (r i) ≠ 0 :=
      fun h => hr i ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
    rw [ha i, Algebra.smul_def, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  refine ⟨d, nonZeroDivisors.ne_zero d.2, secComb (fun i => scal G.hom (a i)) σ,
    fun α => secComb (fun i => scal D.toPre.P.A.hom (a i)) (fun i => f i α), ?_, fun α => ?_, fun e => ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _ (pullback.snd G.hom (jK R)) _ G.hom rfl
      pullback.condition b σ r a d c hc hσ s hs
  · refine secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_
      (Over.w (DegPre.prB D.toPre (FractionRing R))) (fun i => (F i).s α) (fun i => f i α) r a d c hc
      (fun i => hf i α) _ fun j => ?_
    · rw [← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      congr 1
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [fam_sum_f]
      rfl
  · exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)
end GlobalTheory
