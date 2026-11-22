-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.orderedHammingSphere_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:28.914543+00:00
-- url     : https://prove2.me/submissions/7be0f355-668a-4e9b-92a9-310d61ec27c5

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_hammingSphere_card

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} : ∀ s : ℕ,
    (Finset.univ.filter
      (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s)).card =
      q ^ N * (N.choose s * (q - 1) ^ s) := by
  classical
  intro s
  let G : (Fin N → Fin q) → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
    fun x => (Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))
  have h_eq : Finset.univ.filter
      (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s) =
      (Finset.univ : Finset (Fin N → Fin q)).biUnion G := by
    ext xy
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · intro h
      exact ⟨xy.1, xy.2, h, Prod.eta xy⟩
    · rintro ⟨x, y, h, rfl⟩
      exact h
  have h_disj : ((Finset.univ : Finset (Fin N → Fin q)) : Set (Fin N → Fin q)).PairwiseDisjoint
      G := by
    intro x₁ _ x₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨_, _, hp⟩
    exact hne (Prod.mk.inj hp).1.symm
  rw [h_eq, Finset.card_biUnion h_disj]
  have hG_card : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
      (G x).card = N.choose s * (q - 1) ^ s := by
    intro x _
    dsimp [G]
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), hammingSphere_card x s]
  rw [Finset.sum_congr rfl hG_card, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
end HighDimSteinerSpanners.Proofs.CSP
