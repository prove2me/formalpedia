-- Prove2me | solution 1 for GlobalTheory.RowLev.exists_actsBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:32.273431+00:00
-- url     : https://prove2.me/submissions/cfbf17e1-73a5-4090-92f7-d0c801241e11

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_exists_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
variable {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
  {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (fr : ∀ k v, PlFrame I N (g k) (w k v))
namespace GlobalTheory.RowLev
theorem _root_.solution : ∃ ρ : I.Gf → GProd N g Pl, ActsBy fr ρ ∧
    ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ (x * x') = ρ x * ρ x' := by
  choose ρ h1 h2 using fun k v => (fr k v).exists_act
  exact ⟨fun x kv => ρ kv.1 kv.2 x, fun x hx k v => h1 k v x hx,
    fun x hx x' hx' => funext fun kv => h2 kv.1 kv.2 x hx x' hx'⟩
end GlobalTheory.RowLev
