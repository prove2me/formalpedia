-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:46.308045+00:00
-- url     : https://prove2.me/submissions/5620dd0d-6493-41c6-9688-e1fd97c71f52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
variable (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)
omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W]
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
theorem _root_.solution : latBase L 𝔄 ≤ latG F fr L 𝔄 1 := by
  refine Submodule.span_mono ?_
  rintro v ⟨a, ha, x, hx, rfl⟩
  refine ⟨a, ha, x, ⟨toFin F fr x, AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩, ?_⟩, rfl⟩
  simp
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
