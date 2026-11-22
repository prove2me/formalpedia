-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.homQueryMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:28.341804+00:00
-- url     : https://prove2.me/submissions/a2aa4dc6-a899-474a-8f7a-1bd868575069

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} : ∀ z : Fin N → Fin q,
    Function.Injective (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2)) := by
  classical
  intro z uv₁ uv₂ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.1
end HighDimSteinerSpanners.Proofs.CSP
