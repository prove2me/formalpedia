-- Prove2me | solution 1 for GlobalTheory.QuotientDescentTwistedOperators.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:13.936403+00:00
-- url     : https://prove2.me/submissions/c10545de-c1e8-44b2-81d4-25e31085566e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DescMk
import Theorems.Thm_GlobalTheory_QuotientDescentTwistedOperators_desc_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientDescentTwistedOperators
open Topology
namespace GlobalTheory.QuotientDescentTwistedOperators
theorem _root_.solution : ∀ (G : Type) [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_6 : MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology ↥Γ] (K : Set G), IsCompact K → (∀ (x : G), ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [inst_9 : AddCommGroup A] (χ : A → G → ℂ), (∀ (a : A), Continuous (χ a)) → (∀ (a : A) (x y : G), χ a (x + y) = χ a x * χ a y) → (∀ (a b : A) (x : G), χ (a + b) x = χ a x * χ b x) → (∀ (x : G), χ (0 : A) x = (1 : ℂ)) → (∀ (a : A) (x : G), ‖χ a x‖ = (1 : ℝ)) → (∀ (x : G), (∀ (a : A), χ a x = (1 : ℂ)) ↔ x ∈ Γ) → ∀ (Φ : G → ℂ), Continuous Φ → (∀ γ ∈ Γ, ∀ (x : G), Φ (γ + x) = Φ x) → ∀ (ε : ℝ), (0 : ℝ) < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ (x : G), ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ χ hc hmulx hadd hzero hnorm hker Φ hΦ hΦinv ε hε

  have : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have hU : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      ext q
      refine QuotientAddGroup.induction_on q fun x => ?_
      obtain ⟨γ, hγ, hk⟩ := hcov x
      refine ⟨fun _ => ⟨γ + x, hk, ?_⟩, fun _ => Set.mem_univ _⟩
      rw [QuotientAddGroup.eq]
      have : -(γ + x) + x = -γ := by abel
      rw [this]
      exact Γ.neg_mem hγ
    rw [hU]
    exact hK.image continuous_quot_mk
  have hχ0 : ∀ a, χ a 0 = 1 := fun a => (hker 0).2 Γ.zero_mem a
  have hinv : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hmulx, (hker γ).2 hγ a, one_mul]

  let e : A → C(G ⧸ Γ, ℂ) := fun a => desc Γ (χ a) (hc a) (hinv a)
  have he_apply : ∀ a x, e a (QuotientAddGroup.mk x) = χ a x := fun a x =>
    desc_mk Γ (χ a) (hc a) (hinv a) x
  have he_add : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.mul_apply, he_apply, he_apply, he_apply, hadd]
  have he_zero : e 0 = 1 := by
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.one_apply, he_apply, hzero]
  have he_star : ∀ a, star (e a) = e (-a) := by
    intro a
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.star_apply, he_apply, he_apply]
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hadd, neg_add_cancel, hzero]
    have h2 : χ a x * star (χ a x) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    linear_combination (-(star (χ a x))) * h1 + χ (-a) x * h2

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : C(G ⧸ Γ, ℂ)) ∈ S := he_zero ▸ Submodule.subset_span ⟨0, rfl⟩
  have hmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a + b, he_add a b⟩
  have hstar : ∀ f ∈ S, star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨-a, (he_star a).symm⟩
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let B : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hmul f g hf hg
      one_mem' := hone
      add_mem' := fun hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem c hone
      star_mem' := fun {f} hf => hstar f hf }

  have hsep : B.SeparatesPoints := by
    intro q₁ q₂
    refine QuotientAddGroup.induction_on q₁ fun x => QuotientAddGroup.induction_on q₂ fun y => ?_
    intro hne
    have hex : ∃ a, χ a x ≠ χ a y := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hne
      rw [QuotientAddGroup.eq]
      refine (hker _).1 fun a => ?_
      rw [hmulx, ← hall a, ← hmulx, neg_add_cancel, hχ0 a]
    obtain ⟨a, ha⟩ := hex
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    rwa [he_apply, he_apply]

  have hB := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
  let Φq : C(G ⧸ Γ, ℂ) := desc Γ Φ hΦ hΦinv
  have hmem : Φq ∈ closure (B : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hB]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨c, hcg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show g ∈ S from hg)
  refine ⟨c.support, c, fun x => ?_⟩
  have hval : ∑ a ∈ c.support, c a * χ a x = g (QuotientAddGroup.mk x) := by
    rw [← hcg, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ContinuousMap.smul_apply, he_apply, smul_eq_mul]
  rw [hval, ← desc_mk Γ Φ hΦ hΦinv x]
  calc ‖Φq (QuotientAddGroup.mk x) - g (QuotientAddGroup.mk x)‖
      = ‖(Φq - g) (QuotientAddGroup.mk x)‖ := rfl
    _ ≤ ‖Φq - g‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = dist Φq g := (dist_eq_norm _ _).symm
    _ ≤ ε := hdist.le
end GlobalTheory.QuotientDescentTwistedOperators
