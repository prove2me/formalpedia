-- Prove2me | solution 1 for MazurTransfer.scalar_character_line_injectivity_and_range
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:49:12.170996+00:00
-- url     : https://prove2.me/submissions/1015a3e9-ef94-49de-9160-3a2a8ed00c3a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a nonzero eigenvector for a character gives an injective
intertwining map from its scalar representation onto its generated line.
Named downstream consumer: the actual arithmetic13-to-cyclotomic19 norm
kernel short exact sequence.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
noncomputable section
universe u v w
open MazurTransfer.ScalarCharacterLine
namespace MazurTransfer.ScalarCharacterLineProofHelpers20261018
variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

theorem vectorIntertwining_injective (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) (hv0 : v ≠ 0) :
    Function.Injective (vectorIntertwining χ ρ v hv) := by
  exact LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton k hv0)

theorem vectorIntertwining_range (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) :
    LinearMap.range (vectorIntertwining χ ρ v hv).toLinearMap = Submodule.span k {v} :=
  LinearMap.range_toSpanSingleton v

end MazurTransfer.ScalarCharacterLineProofHelpers20261018
theorem solution :
    (∀ {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V] [Module k V] (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) (hv0 : v ≠ 0) ,
    Function.Injective (vectorIntertwining χ ρ v hv)) ∧
    (∀ {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V] [Module k V] (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) ,
    LinearMap.range (vectorIntertwining χ ρ v hv).toLinearMap = Submodule.span k {v}) := by
  exact ⟨MazurTransfer.ScalarCharacterLineProofHelpers20261018.vectorIntertwining_injective, MazurTransfer.ScalarCharacterLineProofHelpers20261018.vectorIntertwining_range⟩
#print axioms solution
