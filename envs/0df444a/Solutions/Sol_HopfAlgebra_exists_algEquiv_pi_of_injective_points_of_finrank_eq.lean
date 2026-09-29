-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1a1549b5-7f33-5c2c-bec0-8e1e70a99762

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq

set_option autoImplicit false

open IsLocalRing

namespace HopfAlgebra
p2m_export "HopfAlgebra" "point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal"
namespace EtaleHalfAux
p2m_open "HopfAlgebra"

section Congr
variable {O H : Type*} [CommRing O] [CommRing H] [HopfAlgebra O H]

theorem convMul_apply_repr (f g : WithConv (H →ₐ[O] O)) (a : H) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr O a ι𝓡) :
    (WithConv.ofConv (f * g)) a = ∑ i ∈ 𝓡.index, (WithConv.ofConv f) (𝓡.left i) * (WithConv.ofConv g) (𝓡.right i) := by

  have h := Coalgebra.Repr.convMul_apply 𝓡 (WithConv.toConv (WithConv.ofConv f).toLinearMap)
    (WithConv.toConv (WithConv.ofConv g).toLinearMap)
  rw [LinearMap.convMul_apply] at h

  exact h

theorem sub_mem_of_congr_left [IsLocalRing O] (y y' z : WithConv (H →ₐ[O] O))
    (hyy : ∀ h : H, y h - y' h ∈ maximalIdeal O) (h : H) :
    (y * z) h - (y' * z) h ∈ maximalIdeal O := by
  classical
  let 𝓡 := Coalgebra.Repr.arbitrary O h
  rw [show (y * z) h = (WithConv.ofConv (y * z)) h from rfl, show (y' * z) h = (WithConv.ofConv (y' * z)) h from rfl,
    convMul_apply_repr y z h 𝓡, convMul_apply_repr y' z h 𝓡, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul]
  exact Ideal.mul_mem_right _ _ (hyy _)

end Congr

theorem eq_of_congr (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (k : ℕ) (htors : ∀ x : WithConv (H →ₐ[O] O), x ^ ℓ ^ k = 1)
    (y y' : WithConv (H →ₐ[O] O)) (hyy : ∀ h : H, y h - y' h ∈ maximalIdeal O)
    (hinv : ∃ z : WithConv (H →ₐ[O] O), y' * z = 1 ∧ z * y' = 1) :
    y = y' := by
  obtain ⟨z, hzr, hzl⟩ := hinv

  have hg1 : ∀ h : H, (y * z) h - algebraMap O O (Coalgebra.counit h) ∈ maximalIdeal O := by
    intro h
    have := sub_mem_of_congr_left y y' z hyy h
    rwa [hzr, show (1 : WithConv (H →ₐ[O] O)) h = algebraMap O O (Coalgebra.counit h) from ?_] at this

    first
    | rfl
    | exact (AlgHom.convOne_apply (R := O) h)
  have hg : y * z = 1 :=
    HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal O ℓ hℓ2 hunif H (y * z)
      hg1 k (htors _)
  calc y = y * (z * y') := by rw [hzl, mul_one]
    _ = (y * z) * y' := by rw [mul_assoc]
    _ = y' := by rw [hg, one_mul]

section CRT
variable {O H : Type*} [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H]

noncomputable def pointIdeal (y : H →ₐ[O] O) : Ideal H := RingHom.ker ((residue O).comp y.toRingHom)

theorem pointIdeal_isMaximal (y : H →ₐ[O] O) : (pointIdeal y).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro t
  obtain ⟨a, rfl⟩ := residue_surjective t
  exact ⟨algebraMap O H a, by simp⟩

theorem pointIdeal_ne (y y' : H →ₐ[O] O) (h : ∃ a : H, y a - y' a ∉ maximalIdeal O) :
    pointIdeal y ≠ pointIdeal y' := by
  obtain ⟨a, ha⟩ := h
  intro heq
  apply ha

  have hmem : a - algebraMap O H (y' a) ∈ pointIdeal y' := by
    show (residue O) (y' (a - algebraMap O H (y' a))) = 0
    simp
  rw [← heq] at hmem
  have : (residue O) (y (a - algebraMap O H (y' a))) = 0 := hmem
  rw [map_sub, AlgHom.commutes] at this
  exact (residue_eq_zero_iff _).mp this

theorem reduction_surjective {ι : Type*} [Finite ι] (y : ι → (H →ₐ[O] O))
    (hdist : ∀ i j, i ≠ j → ∃ a : H, y i a - y j a ∉ maximalIdeal O) :
    Function.Surjective (fun a : H => fun i : ι => residue O (y i a)) := by
  classical
  have hcop : Pairwise fun i j => IsCoprime (pointIdeal (y i)) (pointIdeal (y j)) := fun i j hij => by
    have hne := pointIdeal_ne _ _ (hdist i j hij)
    first
    | exact (pointIdeal_isMaximal (y i)).coprime_of_ne (pointIdeal_isMaximal (y j)) hne
    | exact Ideal.isCoprime_iff_sup_eq.mpr ((pointIdeal_isMaximal (y i)).coprime_of_ne (pointIdeal_isMaximal (y j)) hne)
  intro t

  choose b hb using fun i => residue_surjective (R := O) (t i)
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i => algebraMap O H (b i))
  refine ⟨a, funext fun i => ?_⟩
  have : residue O (y i (a - algebraMap O H (b i))) = 0 := ha i
  rw [map_sub, AlgHom.commutes, map_sub, sub_eq_zero] at this
  show residue O (y i a) = t i
  exact this.trans (hb i)

end CRT

section Eval
variable {O H : Type*} [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H]

def evalAlgHom {ι : Type*} (y : ι → (H →ₐ[O] O)) : H →ₐ[O] (ι → O) :=
  Pi.algHom O (fun _ => O) y

theorem evalAlgHom_apply {ι : Type*} (y : ι → (H →ₐ[O] O)) (a : H) (i : ι) : evalAlgHom y a i = y i a := rfl

theorem surjective_of_surjective_residue {ι : Type*} [Finite ι] [Module.Finite O H]
    (φ : H →ₗ[O] (ι → O))
    (h : Function.Surjective (fun a : H => fun i : ι => residue O (φ a i))) :
    Function.Surjective φ := by
  classical

  have key : (⊤ : Submodule O (ι → O)) ≤ LinearMap.range φ ⊔ maximalIdeal O • ⊤ := by
    intro t _
    obtain ⟨a, ha⟩ := h (fun i => residue O (t i))
    have hdiff : t - φ a ∈ maximalIdeal O • (⊤ : Submodule O (ι → O)) := by

      have hcomp : ∀ i, (t - φ a) i ∈ maximalIdeal O := fun i => by
        have hi := congrFun ha i
        simp only at hi
        rw [Pi.sub_apply, ← residue_eq_zero_iff, map_sub, hi, sub_self]
      haveI : Fintype ι := Fintype.ofFinite ι
      have : t - φ a = ∑ i, (t - φ a) i • (Pi.single i 1 : ι → O) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcomp i) Submodule.mem_top
    have : t = φ a + (t - φ a) := by abel
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self φ a) hdiff
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) key
  exact LinearMap.range_eq_top.mp (top_le_iff.mp hle)

theorem injective_of_surjective_of_finrank_eq {ι : Type*} [Fintype ι] [Module.Finite O H] [Module.Free O H]
    [Nontrivial O] (φ : H →ₗ[O] (ι → O)) (hsurj : Function.Surjective φ)
    (hrank : Module.finrank O H = Fintype.card ι) : Function.Injective φ := by

  have hrank' : Module.finrank O H = Module.finrank O (ι → O) := by rw [hrank, Module.finrank_pi]
  obtain ⟨e⟩ : Nonempty (H ≃ₗ[O] (ι → O)) := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank'
  have hs : Function.Surjective (φ ∘ₗ e.symm.toLinearMap) := hsurj.comp e.symm.surjective
  have hi := OrzechProperty.injective_of_surjective_endomorphism (φ ∘ₗ e.symm.toLinearMap) hs
  intro a b hab
  have := @hi (e a) (e b) (by simpa using hab)
  exact e.injective this

end Eval

theorem exists_algEquiv_pi_of_points' (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (k : ℕ) (htors : ∀ x : WithConv (H →ₐ[O] O), x ^ ℓ ^ k = 1)
    (hinv : ∀ x : WithConv (H →ₐ[O] O), ∃ z, x * z = 1 ∧ z * x = 1)
    {ι : Type*} [Fintype ι] (y : ι → WithConv (H →ₐ[O] O)) (hy : Function.Injective y)
    (hrank : Module.finrank O H = Fintype.card ι) :
    ∃ φ : H ≃ₐ[O] (ι → O), ∀ a i, φ a i = y i a := by
  classical
  haveI : Module.Free O H := Module.free_of_flat_of_isLocalRing

  have hdist : ∀ i j, i ≠ j → ∃ a : H, (WithConv.ofConv (y i)) a - (WithConv.ofConv (y j)) a ∉ maximalIdeal O := by
    intro i j hij
    by_contra hall
    push Not at hall
    exact hij (hy (eq_of_congr O ℓ hℓ2 hunif H k htors (y i) (y j) hall (hinv _)))
  let φ : H →ₐ[O] (ι → O) := evalAlgHom fun i => WithConv.ofConv (y i)
  have hsurj : Function.Surjective φ.toLinearMap :=
    surjective_of_surjective_residue φ.toLinearMap (reduction_surjective (fun i => WithConv.ofConv (y i)) hdist)
  have hinj : Function.Injective φ.toLinearMap := injective_of_surjective_of_finrank_eq φ.toLinearMap hsurj hrank
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a i => rfl⟩

end HopfAlgebra.EtaleHalfAux

open HopfAlgebra.EtaleHalfAux in
theorem solution
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (k : ℕ) (htors : ∀ x : WithConv (H →ₐ[O] O), x ^ ℓ ^ k = 1)
    (hinv : ∀ x : WithConv (H →ₐ[O] O), ∃ z : WithConv (H →ₐ[O] O), x * z = 1 ∧ z * x = 1)
    {ι : Type*} [Fintype ι] (y : ι → WithConv (H →ₐ[O] O)) (hy : Function.Injective y)
    (hrank : Module.finrank O H = Fintype.card ι) :
    ∃ φ : H ≃ₐ[O] (ι → O), ∀ (a : H) (i : ι), φ a i = y i a :=
  exists_algEquiv_pi_of_points' O ℓ hℓ2 hunif H k htors hinv y hy hrank

end S_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq (solution)
