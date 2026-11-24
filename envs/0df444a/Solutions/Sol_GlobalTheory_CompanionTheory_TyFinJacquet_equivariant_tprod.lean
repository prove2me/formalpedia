-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.equivariant_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:37.675026+00:00
-- url     : https://prove2.me/submissions/09c1e676-225e-44e3-bfbe-ceee4496f7b1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
variable {τ : FDRep ℂ (GL ι K)} {b : ι → Fin s} {lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)}
  {Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ}
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (p : parab K b)
    (f : ∀ c, (lam c : Type)) :
    Φ (PiTensorProduct.tprod ℂ fun c => (lam c).ρ (levi K b c p) (f c)) = τ.ρ p.1 (Φ (PiTensorProduct.tprod ℂ f)) := by
  have := LinearMap.congr_fun (heq p) (PiTensorProduct.tprod ℂ f)
  simpa [infl, PiTensorProduct.map_tprod] using this
end GlobalTheory.CompanionTheory.TyFinJacquet
