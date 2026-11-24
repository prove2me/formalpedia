-- Prove2me | solution 1 for GlobalTheory.exists_sum_mul_of_finite_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:52.893475+00:00
-- url     : https://prove2.me/submissions/0ece8baa-f3c5-4b33-953e-71f2ed50b9c8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvCupPairingOfInvCupCharacters
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
namespace GlobalTheory
private lemma pairing_smul_left' {p : ℕ} [NeZero p] {M M' : Type} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod p) M] (β : M →+ M' →+ ZMod p) (a : ZMod p) (v : M) (m' : M') :
    β (a • v) m' = a * β v m' := by
  have h : a • v = a.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val v
  rw [h, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  refine ⟨_, hS.toFinset.biUnion (fun m => (b.repr m).support),
    fun i => (b.coord i).toAddMonoidHom, fun i => β (b i), ?_⟩
  intro m hm m'
  have hsub : (b.repr m).support ⊆ hS.toFinset.biUnion (fun m => (b.repr m).support) :=
    Finset.subset_biUnion_of_mem (fun m => (b.repr m).support) (hS.mem_toFinset.2 hm)
  have hm' : m = ∑ i ∈ (b.repr m).support, b.repr m i • b i := by
    conv_lhs => rw [← b.linearCombination_repr m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hm']
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  simp only [pairing_smul_left', LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
  refine Finset.sum_subset hsub ?_
  intro k _ hk
  have hz : b.repr m k = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.2 h)
  rw [hz, zero_mul]
end GlobalTheory
