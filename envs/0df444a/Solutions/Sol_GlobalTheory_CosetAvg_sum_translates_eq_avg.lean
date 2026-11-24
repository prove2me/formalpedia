-- Prove2me | solution 1 for GlobalTheory.CosetAvg.sum_translates_eq_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:56.033558+00:00
-- url     : https://prove2.me/submissions/cc9d62cc-b94e-4643-abb3-af76088c0892

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
import Theorems.Thm_GlobalTheory_CosetAvg_avg_of_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CosetAvg
open MulAction
namespace GlobalTheory.CosetAvg
theorem _root_.solution : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  intro G M _ _ _ ρ K ι s a R w hR hw hm
  classical
  have hsm : ∀ (k : K) (g : G), k • ((g : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) := fun k g => rfl
  let Y : SubMulAction K (G ⧸ K) :=
    { carrier := {q | ∃ i ∈ s, ∃ k : K, q = k • ((a i : G) : G ⧸ K)}
      smul_mem' := by
        rintro c q ⟨i, hi, k, rfl⟩
        exact ⟨i, hi, c * k, (mul_smul c k _).symm⟩ }
  have hYsub : (Y : Set (G ⧸ K)) ⊆
      ((s.biUnion fun i => (R i).image (QuotientGroup.mk : G → G ⧸ K) : Finset (G ⧸ K)) :
        Set (G ⧸ K)) := by
    rintro q ⟨i, hi, k, rfl⟩
    obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i hi).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨γ, hγ, ?_⟩⟩)
    rw [hsm, QuotientGroup.eq]
    exact hγk
  haveI : Finite Y := (Set.Finite.subset (Finset.finite_toSet _) hYsub).to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  let φ := MulAction.toPermHom K Y
  let H := φ.range
  letI : Fintype H := Fintype.ofFinite H
  have hy : ∀ i ∈ s, ((a i : G) : G ⧸ K) ∈ Y := fun i hi => ⟨i, hi, 1, by simp⟩
  let y : s → Y := fun i => ⟨((a i : G) : G ⧸ K), hy i i.2⟩
  letI : ∀ i, Fintype (orbit H (y i)) := fun i => Fintype.ofFinite _
  let F : s → Y → M := fun i q => ρ (q : G ⧸ K).out (w i)
  have hF : ∀ (i : s) (q : Y) (g : G), (q : G ⧸ K) = (g : G ⧸ K) → F i q = ρ g (w i) := by
    intro i q g hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [F, hq, hk, map_mul, Module.End.mul_apply, hw i i.2 k k.2]
  have hval : ∀ (k : K) (i : s),
      ((((⟨φ k, k, rfl⟩ : H) • y i : Y)) : G ⧸ K) = ((k * a i : G) : G ⧸ K) := fun k i => rfl
  have hinv : ∀ h : H, ∑ i ∈ Finset.univ, F i (h • y i) = ∑ i ∈ Finset.univ, F i (y i) := by
    rintro ⟨_, k, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hF i _ _ (hval k i)),
      Finset.sum_congr rfl (fun i _ => hF i (y i) (a i) rfl)]
    simp only [map_mul, Module.End.mul_apply]
    rw [← map_sum, Finset.sum_coe_sort s (fun i => ρ (a i) (w i)), hm k k.2]
  have hmain := avg_of_invariant (H := H) Finset.univ y F hinv

  have horb : ∀ i : s, ∃ e : (R i) ≃ orbit H (y i),
      ∀ γ : R i, ((e γ : Y) : G ⧸ K) = ((γ : G) : G ⧸ K) := by
    intro i
    have hmemY : ∀ γ ∈ R i, ((γ : G) : G ⧸ K) ∈ Y := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR i i.2).1 γ hγ
      exact ⟨i, i.2, ⟨k₁, hk₁⟩, by rw [hsm, QuotientGroup.mk_mul_of_mem _ hk₂]⟩
    have hmemO : ∀ (γ : G) (hγ : γ ∈ R i), (⟨(γ : G ⧸ K), hmemY γ hγ⟩ : Y) ∈ orbit H (y i) := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, hγe⟩ := (hR i i.2).1 γ hγ
      refine ⟨⟨φ ⟨k₁, hk₁⟩, ⟨k₁, hk₁⟩, rfl⟩, Subtype.ext ?_⟩
      exact (hval _ _).trans ((QuotientGroup.mk_mul_of_mem _ hk₂).symm.trans (congrArg _ hγe.symm))
    let f : R i → orbit H (y i) := fun γ => ⟨⟨(γ : G ⧸ K), hmemY γ γ.2⟩, hmemO γ γ.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ he
        have he' : ((γ : G) : G ⧸ K) = ((γ' : G) : G ⧸ K) :=
          congrArg (fun z : orbit H (y i) => ((z : Y) : G ⧸ K)) he
        rw [QuotientGroup.eq] at he'
        have hu := (hR i i.2).2 γ' ((hR i i.2).1 γ' hγ')
        exact Subtype.ext (hu.unique ⟨hγ, he'⟩ ⟨hγ', by simp⟩)
      · rintro ⟨z, ⟨⟨_, k, rfl⟩, hz⟩⟩
        obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i i.2).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
        refine ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact (QuotientGroup.eq.mpr hγk).trans ((hval k i).symm.trans (congrArg Subtype.val hz))
    exact ⟨Equiv.ofBijective f hbij, fun γ => rfl⟩
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, Finset.sum_congr rfl
    (fun i _ => (hF i (y i) (a i) rfl).symm), hmain]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨e, he⟩ := horb i
  rw [← Fintype.card_congr e, Fintype.card_coe]
  congr 1
  rw [← Finset.sum_coe_sort (R i)]
  exact (Fintype.sum_equiv e _ _ (fun γ => (hF i _ _ (he γ)).symm)).symm
end GlobalTheory.CosetAvg
