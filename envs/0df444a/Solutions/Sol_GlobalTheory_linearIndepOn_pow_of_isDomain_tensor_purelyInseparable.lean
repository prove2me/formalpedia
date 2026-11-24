-- Prove2me | solution 1 for GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:05.926631+00:00
-- url     : https://prove2.me/submissions/acfb3d5f-d400-4700-962d-504da4ca7741

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparabl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k B : Type) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] (p : ℕ) (hp : p.Prime) (hk : CharP k p)
    (hdom : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K →
      IsPurelyInseparable k K → IsDomain (K ⊗[k] B))
    (s : Finset (FractionRing B)) (hs : LinearIndepOn k _root_.id (s : Set (FractionRing B))) :
    LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  classical
  haveI : ExpChar k p := ExpChar.prime hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B) s
  have hb : ∀ x : (s : Set (FractionRing B)), ∃ b : B,
      algebraMap B (FractionRing B) b = (d : B) • (x : FractionRing B) := fun x => hd x x.2
  choose b hb using hb
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hd0 : algebraMap B (FractionRing B) (d : B) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  let φ := IsScalarTower.toAlgHom k B (FractionRing B)
  have hφ : ∀ x, φ x = algebraMap B (FractionRing B) x := fun _ => rfl
  have hb' : ∀ x, φ (b x) = algebraMap B (FractionRing B) (d : B) * (x : FractionRing B) := by
    intro x; rw [hφ, hb, Algebra.smul_def]

  have hbli : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine Fintype.linearIndependent_iff.1 hs g ?_ i
    have h2 : φ (∑ j, g j • b j) = 0 := by rw [hg, map_zero]
    simp only [map_sum, map_smul, hb'] at h2
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (g j) _ _).symm, ← Finset.mul_sum] at h2
    exact (mul_eq_zero.1 h2).resolve_left hd0
  unfold LinearIndepOn
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcB : ∑ j, c j • b j ^ p = 0 := by
    apply hinj
    rw [map_zero, ← hφ]
    simp only [map_sum, map_smul, map_pow, hb', mul_pow]
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (c j) _ _).symm, ← Finset.mul_sum]
    simp only [] at hc
    rw [hc, mul_zero]

  have hroot : ∀ j, ∃ y : AlgebraicClosure k, y ^ p = algebraMap k (AlgebraicClosure k) (c j) :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose y hy using hroot
  let K := IntermediateField.adjoin k (Set.range y)
  haveI hfin : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  have hpi : IsPurelyInseparable k K := by
    refine (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p).2 ?_
    rintro z ⟨j, rfl⟩
    exact ⟨1, by rw [pow_one, hy]; exact ⟨c j, rfl⟩⟩
  haveI := hdom K hfin hpi
  haveI : CharP (K ⊗[k] B) p :=
    charP_of_injective_algebraMap (algebraMap k (K ⊗[k] B)).injective p
  haveI : ExpChar (K ⊗[k] B) p := ExpChar.prime hp
  let y' := fun j => (⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩ : K)
  have hy' : ∀ j, y' j ^ p = algebraMap k K (c j) := by
    intro j; apply Subtype.ext; simp [y', hy]
  have hz : (∑ j, y' j ⊗ₜ[k] b j) ^ p = 0 := by
    rw [sum_pow_char]
    simp only [Algebra.TensorProduct.tmul_pow, hy', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, hcB, TensorProduct.tmul_zero]
  have hz0 : ∑ j, y' j • ((1 : K) ⊗ₜ[k] b j) = 0 := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact pow_eq_zero_iff hp.ne_zero |>.1 hz
  have hli := Module.Flat.linearIndependent_one_tmul (S := K) hbli
  have hyi : y' i = 0 := Fintype.linearIndependent_iff.1 hli y' hz0 i
  have : algebraMap k (AlgebraicClosure k) (c i) = 0 := by
    rw [← hy]
    have : y i = 0 := congrArg Subtype.val hyi
    rw [this, zero_pow hp.ne_zero]
  exact (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).1 this
end GlobalTheory
