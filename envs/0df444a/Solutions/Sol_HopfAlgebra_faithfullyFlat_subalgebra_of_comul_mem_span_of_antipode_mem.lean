-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b102ba29-15e3-5e0f-a854-cbdb8632c8f2

import Mathlib
import Theorems.Thm_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange
import Theorems.Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat
import Theorems.Thm_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

universe u v w

namespace S17Head

abbrev ΔStable {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) : Prop :=
  ∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}

abbrev SStable {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H) : Prop :=
  ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K

theorem algClosed_case {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] (K : Subalgebra k H) (hΔ : ΔStable K) (hS : SStable K) :
    Module.FaithfullyFlat ↥K H := by
  classical

  have key : ∀ K₀ : Subalgebra k H, ΔStable K₀ → SStable K₀ → K₀.FG → Module.FaithfullyFlat ↥K₀ H := by
    intro K₀ hΔ₀ hS₀ hfg
    obtain ⟨p, hp⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hpr | rfl
    · haveI := Fact.mk hpr
      exact HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField p
        (fun K' hΔ' hS' hfg' _ => HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed K' hΔ' hS' hfg')
        K₀ hΔ₀ hS₀ hfg
    · haveI := CharP.charP_to_charZero k
      haveI : IsReduced H := HopfAlgebra.isReduced_of_finiteType_of_charZero k H
      haveI : IsReduced ↥K₀ := isReduced_of_injective K₀.val Subtype.val_injective
      exact HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed K₀ hΔ₀ hS₀ hfg

  let ι := {K₀ : Subalgebra k H // K₀ ≤ K ∧ K₀.FG ∧ ΔStable K₀ ∧ SStable K₀}
  have hex : ∀ s : Finset H, (↑s : Set H) ⊆ K → ∃ i : ι, (↑s : Set H) ⊆ i.1 := by
    intro s hs
    obtain ⟨K₀, hle, hfg, hsub, hΔ₀, hS₀⟩ :=
      HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset K hΔ hS s hs
    exact ⟨⟨K₀, hle, hfg, hΔ₀, hS₀⟩, hsub⟩
  haveI : Nonempty ι := by
    obtain ⟨i, -⟩ := hex ∅ (by simp)
    exact ⟨i⟩
  refine Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat K (fun i : ι => i.1) ?_ (fun i => i.2.1)
    ?_ (fun i => key i.1 i.2.2.2.1 i.2.2.2.2 i.2.2.1)
  ·
    intro i j
    obtain ⟨sᵢ, hsᵢ⟩ := i.2.2.1
    obtain ⟨sⱼ, hsⱼ⟩ := j.2.2.1
    have hsub : (↑(sᵢ ∪ sⱼ) : Set H) ⊆ K := by
      rw [Finset.coe_union]
      refine Set.union_subset ?_ ?_
      · exact (Algebra.subset_adjoin.trans (le_of_eq hsᵢ : Algebra.adjoin k ↑sᵢ ≤ i.1)).trans i.2.1
      · exact (Algebra.subset_adjoin.trans (le_of_eq hsⱼ : Algebra.adjoin k ↑sⱼ ≤ j.1)).trans j.2.1
    obtain ⟨m, hm⟩ := hex (sᵢ ∪ sⱼ) hsub
    refine ⟨m, ?_, ?_⟩
    · show i.1 ≤ m.1
      rw [← hsᵢ]
      exact Algebra.adjoin_le ((Finset.coe_subset.mpr Finset.subset_union_left).trans hm)
    · show j.1 ≤ m.1
      rw [← hsⱼ]
      exact Algebra.adjoin_le ((Finset.coe_subset.mpr Finset.subset_union_right).trans hm)
  ·
    intro x hx
    obtain ⟨i, hi⟩ := hex {x} (by simpa using hx)
    exact ⟨i, hi (by simp)⟩

theorem stable_range {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) (hΔ : ΔStable K) (hS : SStable K) (k' : Type w) [Field k'] [Algebra k k'] :
    ΔStable ((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) ∧
      SStable ((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) := by
  classical
  set φ := Algebra.TensorProduct.map (AlgHom.id k' k') K.val with hφ
  have hφ_tmul : ∀ (c : k') (y : ↥K), φ (c ⊗ₜ[k] y) = c ⊗ₜ[k] (y : H) := fun c y => by
    rw [hφ, Algebra.TensorProduct.map_tmul]; rfl
  have hmem : ∀ (c : k') (y : H), y ∈ K → c ⊗ₜ[k] y ∈ φ.range := fun c y hy =>
    ⟨c ⊗ₜ[k] ⟨y, hy⟩, hφ_tmul c ⟨y, hy⟩⟩
  set P : Submodule k' ((k' ⊗[k] H) ⊗[k'] (k' ⊗[k] H)) :=
    Submodule.span k' {t | ∃ a ∈ φ.range, ∃ b ∈ φ.range, t = a ⊗ₜ[k'] b} with hP
  constructor
  · rintro _ ⟨t, rfl⟩
    show Coalgebra.comul (R := k') (φ t) ∈ P
    induction t with
    | zero => rw [map_zero, map_zero]; exact P.zero_mem
    | add x y hx hy => rw [map_add, map_add]; exact P.add_mem hx hy
    | tmul c y =>
        rw [hφ_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply]

        refine Submodule.span_induction ?_ ?_ ?_ ?_ (hΔ (y : H) y.2)
        · rintro _ ⟨a, ha, b, hb, rfl⟩
          rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
          exact Submodule.subset_span ⟨_, hmem 1 a ha, _, hmem c b hb, rfl⟩
        · rw [TensorProduct.tmul_zero, map_zero]; exact P.zero_mem
        · intro z₁ z₂ _ _ h₁ h₂
          rw [TensorProduct.tmul_add, map_add]; exact P.add_mem h₁ h₂
        · intro r z _ hz
          rw [TensorProduct.tmul_smul, ← algebraMap_smul k' r, LinearEquiv.map_smul]
          exact P.smul_mem _ hz
  · rintro _ ⟨t, rfl⟩
    show HopfAlgebra.antipode k' (φ t) ∈ φ.range
    induction t with
    | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
    | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
    | tmul c y =>
        rw [hφ_tmul, TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
          CommSemiring.antipode_eq_id, LinearMap.id_apply]
        exact hmem c _ (hS (y : H) y.2)

end S17Head

open S17Head in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) :
    Module.FaithfullyFlat ↥K H := by
  obtain ⟨hΔ', hS'⟩ := stable_range K hΔ hS (AlgebraicClosure k)
  exact Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange K (AlgebraicClosure k)
    (algClosed_case _ hΔ' hS')

end S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem (solution)
