-- Prove2me | solution 1 for GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:26.352624+00:00
-- url     : https://prove2.me/submissions/3afd75da-e4bc-4cba-b881-e9bf47cdfed1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_spec
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_exists_evalAt_ne_zero
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_smul
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_add
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_sub
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_expand_mem
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_nat_mul_add_inj
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_finsupp_coord
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_vector_val
import Theorems.Thm_GlobalTheory_T_exists_injective_values_on_finrank_family
import Theorems.Thm_GlobalTheory_T_linearIndependent_of_injective_valuationLike


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open HilbertSamuelPS MvPowerSeries
namespace GlobalTheory
theorem _root_.solution :
    ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  intro D n A _ _ φ x c hinj hx F G _ _ m hm hG
  classical
  have h1 : ∀ (c : ℂ) (u : A), c ≠ 0 → val φ (c • u) = val φ u := fun c u hc => val_smul c u hc
  have h2 := val_add hinj
  have h3 := val_sub hinj
  obtain ⟨b, hbF, hbinj⟩ := GlobalTheory.T.exists_injective_values_on_finrank_family ℂ A _ (val φ) h1 h2 h3 F
  have hbne : ∀ i, ∃ k, evalAt φ k (b i) ≠ 0 := fun i => exists_evalAt_ne_zero hinj (hbF i).2
  have hex : ∀ i, ∃ e : Fin D →₀ ℕ, lexOrder (evalAt φ (firstIdx φ (b i)) (b i)) =
      ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) :=
    fun i => exists_finsupp_eq_lexOrder_of_ne_zero (firstIdx_spec φ (hbne i)).1
  choose e he using hex
  let w : Fin (Module.finrank ℂ F) × (Fin D → Fin m) → A := fun p =>
    b p.1 ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ ((p.2 d : ℕ))
  have hwv := fun p : Fin (Module.finrank ℂ F) × (Fin D → Fin m) =>
    vector_val (φ := φ) hx hm.ne' (hbne p.1) (he p.1) (fun d => (p.2 d : ℕ))
  have hwinj : Function.Injective (fun p => val φ (w p)) := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ h
    have e1 := (hwv (i, a)).2
    have e2 := (hwv (i', a')).2
    have h'' := e1.symm.trans (h.trans e2)
    have h' := congrArg ofLex h''
    simp only [ofLex_toLex, Prod.mk.injEq, WithTop.coe_inj, toLex_inj] at h'
    obtain ⟨hk, hs⟩ := h'
    have hcoord : ∀ d, e i d = e i' d ∧ (a d : ℕ) = a' d := fun d => by
      have := congrArg (fun f : Fin D →₀ ℕ => f d) hs
      simp only [finsupp_coord] at this
      exact nat_mul_add_inj (a d).2 (a' d).2 this
    have hee : e i = e i' := Finsupp.ext fun d => (hcoord d).1
    have hii : i = i' := hbinj (by
      show toLex (firstIdx φ (b i), lexOrder (evalAt φ (firstIdx φ (b i)) (b i))) =
        toLex (firstIdx φ (b i'), lexOrder (evalAt φ (firstIdx φ (b i')) (b i')))
      rw [he i, he i', hk, hee])
    subst hii
    have haa : a = a' := funext fun d => Fin.ext (hcoord d).2
    rw [haa]
  have hli : LinearIndependent ℂ w :=
    GlobalTheory.T.linearIndependent_of_injective_valuationLike ℂ A _ _ (val φ) h1 h2 w (fun p => (hwv p).1) hwinj
  have hwG : ∀ p, w p ∈ G := fun p =>
    expand_mem x c F G m hG (b p.1) (hbF p.1).1 (fun d => (p.2 d : ℕ)) (fun d => (p.2 d).2)
  let wG : Fin (Module.finrank ℂ F) × (Fin D → Fin m) → G := fun p => ⟨w p, hwG p⟩
  have hliG : LinearIndependent ℂ wG := LinearIndependent.of_comp G.subtype hli
  have := hliG.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fun] using this
end GlobalTheory
