-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_families_span_generate_valuationRings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:16.364234+00:00
-- url     : https://prove2.me/submissions/498c8b53-95b3-4fa9-8cb1-1fe673314847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanGenerateValuationRings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanGenerateValuationRingsStatement
import Theorems.Thm_GlobalTheory_FamGen_exists_span_generate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  first | exact @GlobalTheory.FamGen.exists_span_generate | exact GlobalTheory.FamGen.exists_span_generate | (intros; apply GlobalTheory.FamGen.exists_span_generate <;> assumption)
end _root_.GlobalTheory.T
