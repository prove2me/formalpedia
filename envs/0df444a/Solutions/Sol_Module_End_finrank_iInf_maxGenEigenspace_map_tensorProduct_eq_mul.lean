-- Prove2me | solution 1 for Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ec459003-b6fb-5aba-b858-e7bb106e8701

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul

set_option autoImplicit false

open scoped TensorProduct

namespace GeneigTensorAux

open Module Module.End

variable {F : Type} [Field F]

theorem comap_maxGenEigenspace_eq_of_comm
    {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (ι : X →ₗ[F] Y) (hι : Function.Injective ι) (f' : Module.End F X) (f : Module.End F Y)
    (h : ι ∘ₗ f' = f ∘ₗ ι) (μ : F) :
    (f.maxGenEigenspace μ).comap ι = f'.maxGenEigenspace μ := by
  have hc : ∀ y, f (ι y) = ι (f' y) := fun y => (LinearMap.congr_fun h y).symm
  have hk : ∀ (k : ℕ) (x : X), ((f - μ • (1 : Module.End F Y)) ^ k) (ι x) =
      ι (((f' - μ • (1 : Module.End F X)) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [LinearMap.sub_apply, hc]
  ext x
  simp only [Submodule.mem_comap, Module.End.mem_maxGenEigenspace, hk, map_eq_zero_iff ι hι]

variable {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

private noncomputable def _root_.GeneigTensorAux.coord (M : Type) [AddCommGroup M] [Module F M]
    (b : Fin (Module.finrank F W)) : M ⊗[F] W →ₗ[F] M :=
  (TensorProduct.rid F M).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.id : M →ₗ[F] M) ((Module.finBasis F W).coord b)

p2m_export "GeneigTensorAux" "coord"
theorem coord_tmul (M : Type) [AddCommGroup M] [Module F M]
    (b : Fin (Module.finrank F W)) (m : M) (w : W) :
    coord M b (m ⊗ₜ[F] w) = (Module.finBasis F W).repr w b • m := by
  simp [coord, Module.Basis.coord]

theorem coord_map {M M' : Type} [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F M']
    (g : M' →ₗ[F] M) (b : Fin (Module.finrank F W)) (x : M' ⊗[F] W) :
    coord M b (TensorProduct.map g (LinearMap.id : W →ₗ[F] W) x) = g (coord M' b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m w => simp [coord_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem sum_coord_tmul (M : Type) [AddCommGroup M] [Module F M] (x : M ⊗[F] W) :
    ∑ b, coord M b x ⊗ₜ[F] (Module.finBasis F W) b = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m w =>
      simp_rw [coord_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
      rw [Module.Basis.sum_repr]
  | add x y hx hy =>
      simp_rw [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

theorem mem_range_map_subtype_iff (M : Type) [AddCommGroup M] [Module F M]
    (P : Submodule F M) (x : M ⊗[F] W) :
    x ∈ LinearMap.range (TensorProduct.map P.subtype (LinearMap.id : W →ₗ[F] W)) ↔
      ∀ b, coord M b x ∈ P := by
  constructor
  · rintro ⟨y, rfl⟩ b
    rw [coord_map]
    exact (coord (↥P) b y).2
  · intro h
    rw [← sum_coord_tmul M x]
    refine Submodule.sum_mem _ fun b _ => ?_
    exact ⟨(⟨coord M b x, h b⟩ : ↥P) ⊗ₜ[F] (Module.finBasis F W) b, by simp⟩

theorem map_subtype_id_injective (M : Type) [AddCommGroup M] [Module F M] (P : Submodule F M) :
    Function.Injective (TensorProduct.map P.subtype (LinearMap.id : W →ₗ[F] W)) := by
  intro y y' hyy
  rw [← sub_eq_zero] at hyy ⊢
  rw [← map_sub] at hyy
  generalize y - y' = z at hyy ⊢
  have hz : ∀ b, coord (↥P) b z = 0 := fun b => by
    apply P.injective_subtype
    rw [← coord_map, hyy, map_zero, map_zero]
  rw [← sum_coord_tmul (↥P) z]
  simp [hz]

omit [FiniteDimensional F W] in
theorem map_sub_smul_one (M : Type) [AddCommGroup M] [Module F M] (f : Module.End F M) (μ : F) :
    TensorProduct.map f (LinearMap.id : W →ₗ[F] W) - μ • 1 =
      TensorProduct.map (f - μ • 1) (LinearMap.id : W →ₗ[F] W) := by
  apply TensorProduct.ext'
  intro m w
  simp [TensorProduct.sub_tmul, TensorProduct.smul_tmul']

omit [FiniteDimensional F W] in
theorem map_sub_smul_one_pow (M : Type) [AddCommGroup M] [Module F M] (f : Module.End F M) (μ : F)
    (k : ℕ) :
    (TensorProduct.map f (LinearMap.id : W →ₗ[F] W) - μ • 1) ^ k =
      TensorProduct.map ((f - μ • 1) ^ k) (LinearMap.id : W →ₗ[F] W) := by
  rw [map_sub_smul_one]
  exact LinearMap.rTensor_pow (f - μ • 1) k

theorem mem_maxGenEigenspace_map_id_iff (M : Type) [AddCommGroup M] [Module F M]
    (f : Module.End F M) (μ : F) (x : M ⊗[F] W) :
    x ∈ Module.End.maxGenEigenspace (TensorProduct.map f (LinearMap.id : W →ₗ[F] W)) μ ↔
      ∀ b, coord M b x ∈ Module.End.maxGenEigenspace f μ := by
  simp only [Module.End.mem_maxGenEigenspace, map_sub_smul_one_pow]
  constructor
  · rintro ⟨k, hk⟩ b
    exact ⟨k, by rw [← coord_map, hk, map_zero]⟩
  · intro h
    choose k hk using h
    refine ⟨∑ b, k b, ?_⟩
    rw [← sum_coord_tmul M x, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    have hle : k b ≤ ∑ b', k b' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
    rw [hd, pow_add, Module.End.mul_apply, hk b, map_zero, TensorProduct.zero_tmul]

theorem iInf_maxGenEigenspace_map_id_eq_range (M : Type) [AddCommGroup M] [Module F M]
    {ι : Type} (A : ι → Module.End F M) (μ : ι → F) :
    (⨅ i, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) =
      LinearMap.range (TensorProduct.map (⨅ i, Module.End.maxGenEigenspace (A i) (μ i)).subtype
        (LinearMap.id : W →ₗ[F] W)) := by
  ext x
  simp only [Submodule.mem_iInf, mem_maxGenEigenspace_map_id_iff, mem_range_map_subtype_iff]
  exact forall_comm

theorem map_id_subtype_injective (M : Type) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (N : Type) [AddCommGroup N] [Module F N] (P : Submodule F N) :
    Function.Injective (TensorProduct.map (LinearMap.id : M →ₗ[F] M) P.subtype) := by
  have h : TensorProduct.map (LinearMap.id : M →ₗ[F] M) P.subtype =
      (TensorProduct.comm F N M).toLinearMap ∘ₗ
        TensorProduct.map P.subtype (LinearMap.id : M →ₗ[F] M) ∘ₗ
          (TensorProduct.comm F M ↥P).toLinearMap := by
    apply TensorProduct.ext'
    intro m p
    simp
  rw [h]
  exact (TensorProduct.comm F N M).injective.comp
    ((map_subtype_id_injective (W := M) N P).comp (TensorProduct.comm F M ↥P).injective)

theorem iInf_maxGenEigenspace_id_map_eq_range (M : Type) [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (N : Type) [AddCommGroup N] [Module F N]
    {κ : Type} (B : κ → Module.End F N) (ν : κ → F) :
    (⨅ j, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : M →ₗ[F] M) (B j)) (ν j)) =
      LinearMap.range (TensorProduct.map (LinearMap.id : M →ₗ[F] M)
        (⨅ j, Module.End.maxGenEigenspace (B j) (ν j)).subtype) := by
  have h1 : ∀ j, (Module.End.maxGenEigenspace
        (TensorProduct.map (B j) (LinearMap.id : M →ₗ[F] M)) (ν j)).comap
        (TensorProduct.comm F M N).toLinearMap =
      Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : M →ₗ[F] M) (B j)) (ν j) :=
    fun j => comap_maxGenEigenspace_eq_of_comm _ (TensorProduct.comm F M N).injective _ _
      (by apply TensorProduct.ext'; intro m n; simp) (ν j)
  have hc : (TensorProduct.comm F M N).symm.toLinearMap ∘ₗ
      TensorProduct.map (⨅ j, Module.End.maxGenEigenspace (B j) (ν j)).subtype
        (LinearMap.id : M →ₗ[F] M) =
      TensorProduct.map (LinearMap.id : M →ₗ[F] M)
        (⨅ j, Module.End.maxGenEigenspace (B j) (ν j)).subtype ∘ₗ
        (TensorProduct.comm F (↥(⨅ j, Module.End.maxGenEigenspace (B j) (ν j))) M).toLinearMap := by
    apply TensorProduct.ext'
    intro t m
    simp
  calc (⨅ j, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : M →ₗ[F] M) (B j)) (ν j))
      = (⨅ j, Module.End.maxGenEigenspace
          (TensorProduct.map (B j) (LinearMap.id : M →ₗ[F] M)) (ν j)).comap
          (TensorProduct.comm F M N).toLinearMap := by
        rw [Submodule.comap_iInf]
        exact (iInf_congr h1).symm
    _ = (LinearMap.range (TensorProduct.map (⨅ j, Module.End.maxGenEigenspace (B j) (ν j)).subtype
          (LinearMap.id : M →ₗ[F] M))).comap (TensorProduct.comm F M N).toLinearMap := by
        rw [iInf_maxGenEigenspace_map_id_eq_range (W := M) N B ν]
    _ = LinearMap.range (TensorProduct.map (LinearMap.id : M →ₗ[F] M)
          (⨅ j, Module.End.maxGenEigenspace (B j) (ν j)).subtype) := by
        rw [Submodule.comap_equiv_eq_map_symm, ← LinearMap.range_comp, hc,
          LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

end GeneigTensorAux

theorem solution
    (F : Type) [Field F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι κ : Type} (A : ι → Module.End F V) (μ : ι → F) (B : κ → Module.End F W) (ν : κ → F) :
    Module.finrank F
      ↥((⨅ i : ι, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) ⊓
        (⨅ j : κ, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j))) =
    Module.finrank F ↥(⨅ i : ι, Module.End.maxGenEigenspace (A i) (μ i)) *
      Module.finrank F ↥(⨅ j : κ, Module.End.maxGenEigenspace (B j) (ν j)) := by
  rw [GeneigTensorAux.iInf_maxGenEigenspace_map_id_eq_range V A μ, ← Submodule.map_comap_eq,
    Submodule.comap_iInf]
  have hιS : Function.Injective (TensorProduct.map
      (⨅ i, Module.End.maxGenEigenspace (A i) (μ i)).subtype (LinearMap.id : W →ₗ[F] W)) :=
    GeneigTensorAux.map_subtype_id_injective V _
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hιS _)]
  have h2 : ∀ j, (Module.End.maxGenEigenspace
        (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j)).comap
        (TensorProduct.map (⨅ i, Module.End.maxGenEigenspace (A i) (μ i)).subtype
          (LinearMap.id : W →ₗ[F] W)) =
      Module.End.maxGenEigenspace (TensorProduct.map
        (LinearMap.id : ↥(⨅ i, Module.End.maxGenEigenspace (A i) (μ i)) →ₗ[F]
          ↥(⨅ i, Module.End.maxGenEigenspace (A i) (μ i))) (B j)) (ν j) := fun j =>
    GeneigTensorAux.comap_maxGenEigenspace_eq_of_comm _ hιS _ _
      (by rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.id_comp, LinearMap.comp_id]) (ν j)
  rw [iInf_congr h2, GeneigTensorAux.iInf_maxGenEigenspace_id_map_eq_range _ W B ν,
    LinearMap.finrank_range_of_inj (GeneigTensorAux.map_id_subtype_injective _ W _),
    Module.finrank_tensorProduct]

end S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
end P2MW
export P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul (solution)
