-- Prove2me | solution 1 for GlobalTheory.DI.decomp_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:02.271157+00:00
-- url     : https://prove2.me/submissions/7edf4e46-71c7-4412-9020-bc9747f2a9aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CupProductFiltrationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductVanishAboveDegreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartierPropertyAtSignMulFactorialScalingStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosedStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_ExistsFrobeniusSplittingDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductLeadingTermStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingIntegralFormsBoundStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingLocalIntegrality
import Theorems.Thm_GlobalTheory_T_cartierPropertyAt_sign_mul_factorial_scaling
import Theorems.Thm_GlobalTheory_T_cechAntisymmetrizedCupProduct_leading_term
import Theorems.Thm_GlobalTheory_T_cechAntisymmetrizedCupProduct_vanish_above_degree
import Theorems.Thm_GlobalTheory_T_cechZero_of_hypZero_of_cartier
import Theorems.Thm_GlobalTheory_T_exists_frobenius_splitting_datum
import Theorems.Thm_GlobalTheory_T_frobenius_splitting_closed
import Theorems.Thm_GlobalTheory_T_splitting_integral_forms_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
private theorem forms_mono' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {B B' : Set K} {L L' : Set V} (hB : B ⊆ B') (hL : L ⊆ L') (q : ℕ) :
    forms B L q ≤ forms B' L' q := by
  unfold forms
  apply AddSubgroup.closure_mono
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, hB hb, v, fun k => hL (hv k), rfl⟩
private theorem iota_mem_forms_one' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (A : Subring K) (w : V) : ExteriorAlgebra.ι K w ∈ forms (A : Set K) (Set.univ : Set V) 1 := by
  unfold forms
  apply AddSubgroup.subset_closure
  refine ⟨1, A.one_mem, fun _ => w, fun _ => trivial, ?_⟩
  rw [one_smul, ExteriorAlgebra.ιMulti_apply]
  simp
private theorem psmul_zero' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) [CharP K p] (x : ExteriorAlgebra K V) : p • x = 0 := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap K (ExteriorAlgebra K V)), CharP.cast_eq_zero, map_zero,
    zero_mul]
end GlobalTheory.DI
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro K _ V _ _ ι _ p _ _ d f h γ P U A B L N T hd hD hγ hNm hTm hTd hNu hNp hNU hT hfA hhA hC
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_frobenius_splitting_datum p d f h hD
  obtain ⟨h0, hcl⟩ := GlobalTheory.T.frobenius_splitting_closed p d f h Φ hd hD hΦ
  have hvan := (GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree p f h).2 Φ hΦ
  apply GlobalTheory.T.cechZero_of_hypZero_of_cartier d N T Φ hd.sq hNm hTm hTd h0 hcl
  · intro a u t x hu htu hx
    have hxu : x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a := hNu a u hu hx
    refine ⟨fun q hq => ?_, fun hlt => hvan a x hxu t hlt⟩
    apply hT q u _ hu
    · have := GlobalTheory.T.splitting_integral_forms_bound p f h Φ (⊤ : Subring K) Set.univ Set.univ t hΦ
        (fun i _ v _ => iota_mem_forms_one' ⊤ (f i v)) (fun _ _ _ _ _ _ => Subring.mem_top _) a q t
        subset_rfl hq x hxu
      exact forms_mono' (Set.subset_univ _) subset_rfl q this
    · intro y hy
      exact GlobalTheory.T.splitting_integral_forms_bound p f h Φ (A y) (B y) (L y) u hΦ (hfA u y hy) (hhA u y hy) a q t htu hq x
        (hNU a u hu y hy hx)
  · intro s j hj
    have hs : s.Nonempty := ⟨j, hj⟩
    exact GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling p d (γ j).toAddMonoidHom (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)
      (psmul_zero' p) (fun a ha => hNp a s hs ha)
      (fun a x hx => (GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term p f h).2 Φ j (γ j) hΦ (hγ j) a x (hNu a s hs hx)) (hC s j hj)
end GlobalTheory.DI
