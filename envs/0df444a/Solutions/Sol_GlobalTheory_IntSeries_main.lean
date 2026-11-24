-- Prove2me | solution 1 for GlobalTheory.IntSeries.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:42.729148+00:00
-- url     : https://prove2.me/submissions/e5f437cd-0c39-4757-b2bb-0e256b9e0a40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Theorems.Thm_GlobalTheory_IntSeries_intAA_map
import Theorems.Thm_GlobalTheory_IntSeries_intAA_add
import Theorems.Thm_GlobalTheory_IntSeries_intAA_sub
import Theorems.Thm_GlobalTheory_IntSeries_intAA_mul
import Theorems.Thm_GlobalTheory_IntSeries_intAA_pderiv
import Theorems.Thm_GlobalTheory_IntSeries_intAA_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}
namespace GlobalTheory.IntSeries
theorem _root_.solution : ∀ (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k],
  (∀ (σ : Type) (f g : MvPowerSeries σ k), IntAA (R := R) k f → IntAA (R := R) k g → IntAA (R := R) k (f + g) ∧ IntAA (R := R) k (f - g) ∧ IntAA (R := R) k (f * g)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ k) (s : σ), IntAA (R := R) k f → IntAA (R := R) k (pderiv k s f)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ R), IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f)) ∧
  (∀ (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ k) (f : MvPowerSeries σ k), (∀ s, constantCoeff (a s) = 0) → (∀ s, IntAA (R := R) k (a s)) → IntAA (R := R) k f → IntAA (R := R) k (MvPowerSeries.subst a f)) :=
  fun _ _ _ _ _ =>
    ⟨fun _ _ _ hf hg => ⟨intAA_add hf hg, intAA_sub hf hg, intAA_mul hf hg⟩,
      fun _ _ s hf => intAA_pderiv s hf, fun _ f => intAA_map f,
      fun _ _ _ _ _ ha hai hf => intAA_subst ha hai hf⟩
end GlobalTheory.IntSeries
