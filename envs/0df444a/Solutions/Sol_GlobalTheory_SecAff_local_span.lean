-- Prove2me | solution 1 for GlobalTheory.SecAff.local_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:30:00.903951+00:00
-- url     : https://prove2.me/submissions/8e7746c2-d7f7-4a35-922f-0655fed2eb66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_isPullSec_iff
import Theorems.Thm_GlobalTheory_SecAff_span_of_retract
import Theorems.Thm_GlobalTheory_SecAff_exists_spec_retract

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
namespace GlobalTheory.SecAff
theorem _root_.solution (H : SecBaseChangeSt) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (hn : 1 ≤ n) (p : S) : ∃ V : S.Opens, p ∈ V ∧
      ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V),
        ∀ (T' : Over S) [IsAffine T'.left] (g : T' ⟶ overRes (T := baseOver S) V),
          Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull P.A P.L n g (b i)) = ⊤ := by
  obtain ⟨V, hp, b, hb⟩ := H S P n hn p
  refine ⟨V, hp, fun i => SecM.ofSec P.A (b i), fun T' _ g => ?_⟩
  obtain ⟨R, _, t, e, e', h1, rfl⟩ := exists_spec_retract g
  exact span_of_retract P.A P.L n e e' h1 (homAt t) _ (hb R t
    (fun i => SecM.toSec P.A (pull P.A P.L n (homAt t) (SecM.ofSec P.A (b i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)).2
end GlobalTheory.SecAff
