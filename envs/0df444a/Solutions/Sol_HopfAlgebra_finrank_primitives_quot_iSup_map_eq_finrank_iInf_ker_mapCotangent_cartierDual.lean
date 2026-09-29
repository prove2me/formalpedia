-- Prove2me | solution 1 for HopfAlgebra.finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d453f374-2c20-5c64-98c2-7837ab0d43b0

import Mathlib
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace PRIMCOUNT

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "ε" => Coalgebra.counit (R := k) (A := A)

private theorem mem_primitives_iff (φ : CartierDual k A) :
    φ ∈ primitives k (CartierDual k A) ↔ ∀ a b : A, φ (a * b) = φ a * ε b + ε a * φ b := by
  have hmem : φ ∈ primitives k (CartierDual k A) ↔
      Coalgebra.comul (R := k) φ = φ ⊗ₜ[k] (1 : CartierDual k A) + (1 : CartierDual k A) ⊗ₜ[k] φ := by
    change φ ∈ LinearMap.ker _ ↔ _
    rw [LinearMap.mem_ker]
    erw [LinearMap.sub_apply, LinearMap.sub_apply]
    rw [sub_sub]
    exact ⟨fun h => sub_eq_zero.mp h, fun h => sub_eq_zero.mpr h⟩
  have hpair : ∀ a b : A, TensorProduct.dualDistrib k A A
      (TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap
        (φ ⊗ₜ[k] (1 : CartierDual k A) + (1 : CartierDual k A) ⊗ₜ[k] φ)) (a ⊗ₜ[k] b) = φ a * ε b + ε a * φ b := by
    intro a b
    rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add, LinearMap.add_apply,
      TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
    rfl
  rw [hmem]
  constructor
  · intro h a b
    rw [← CartierDual.comul_pairing φ a b, h, hpair]
  · intro h
    exact CartierDual.tmul_eq_of_pairing_eq fun a b => by rw [CartierDual.comul_pairing, hpair, h]

variable {k A}

private theorem apply_one_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) : φ 1 = 0 := by
  have h := (mem_primitives_iff k A φ).1 hφ 1 1
  rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h

  have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

private theorem apply_mul_of_counit_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (a x : A)
    (hx : ε x = 0) : φ (a * x) = ε a * φ x := by
  rw [(mem_primitives_iff k A φ).1 hφ, hx, mul_zero, zero_add]

private theorem apply_mul_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (x y : A)
    (hx : ε x = 0) (hy : ε y = 0) : φ (x * y) = 0 := by
  rw [apply_mul_of_counit_eq_zero hφ x y hy, hx, zero_mul]

variable (k A)

private abbrev I : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
private theorem mem_I {x : A} : x ∈ I k A ↔ ε x = 0 := RingHom.mem_ker

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
private theorem sub_algebraMap_counit_mem (a : A) : a - algebraMap k A (ε a) ∈ I k A := by
  rw [mem_I, map_sub]
  change ε a - Bialgebra.counitAlgHom k A (algebraMap k A (ε a)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

private noncomputable def restrictI (φ : CartierDual k A) : ↥(I k A) →ₗ[k] k :=
  (CartierDual.toDual k A φ).comp ((I k A).subtype.restrictScalars k)

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
@[scoped simp] private theorem restrictI_apply (φ : CartierDual k A) (x : ↥(I k A)) : restrictI k A φ x = φ x := rfl

private theorem restrictI_vanishes {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) :
    ((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k ≤ LinearMap.ker (restrictI k A φ) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  rw [LinearMap.mem_ker, restrictI_apply]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    change φ (a • (y : A)) = 0
    rw [smul_eq_mul]
    exact apply_mul_eq_zero hφ a y ((mem_I k A).1 ha) ((mem_I k A).1 y.2)
  · intro x y hx hy
    change φ ((x : A) + y) = 0
    rw [map_add]
    change φ x + φ y = 0
    rw [hx, hy, add_zero]

private noncomputable def toCotDual {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) :
    Module.Dual k (cotangentSpace k A) :=
  ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ (restrictI k A φ) (restrictI_vanishes k A hφ)).comp
    (Submodule.Quotient.restrictScalarsEquiv k ((I k A) • ⊤ : Submodule A ↥(I k A))).symm.toLinearMap

private theorem toCotDual_toCotangent {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (x : ↥(I k A)) :
    toCotDual k A hφ ((I k A).toCotangent x) = φ x := by
  change ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ (restrictI k A φ) (restrictI_vanishes k A hφ))
    ((Submodule.Quotient.restrictScalarsEquiv k ((I k A) • ⊤ : Submodule A ↥(I k A))).symm (Submodule.Quotient.mk x)) = φ x
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

private noncomputable def ofCotDualFun (ψ : Module.Dual k (cotangentSpace k A)) : A →ₗ[k] k where
  toFun a := ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), sub_algebraMap_counit_mem k A a⟩)
  map_add' a b := by
    rw [← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    change a + b - algebraMap k A (ε (a + b)) = (a - algebraMap k A (ε a)) + (b - algebraMap k A (ε b))
    rw [map_add, map_add]; abel
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]
    congr 2
    apply Subtype.ext
    change c • a - algebraMap k A (ε (c • a)) = c • (a - algebraMap k A (ε a))
    rw [map_smul, smul_eq_mul, smul_sub, Algebra.smul_def, Algebra.smul_def, map_mul]

private theorem ofCotDualFun_mem (ψ : Module.Dual k (cotangentSpace k A)) :
    CartierDual.ofDual k A (ofCotDualFun k A ψ) ∈ primitives k (CartierDual k A) := by
  rw [mem_primitives_iff]
  intro a b
  change ofCotDualFun k A ψ (a * b) = ofCotDualFun k A ψ a * ε b + ε a * ofCotDualFun k A ψ b
  change ψ ((I k A).toCotangent ⟨a * b - algebraMap k A (ε (a * b)), _⟩) =
    ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), _⟩) * ε b + ε a * ψ ((I k A).toCotangent ⟨b - algebraMap k A (ε b), _⟩)
  have hlin : ∀ (c : k) (y : ↥(I k A)), c • (I k A).toCotangent y = (I k A).toCotangent (c • y) := fun c y =>
    (((I k A).toCotangent.restrictScalars k).map_smul c y).symm
  rw [mul_comm (ψ _) (ε b)]
  change _ = ε b • ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), sub_algebraMap_counit_mem k A a⟩) +
    ε a • ψ ((I k A).toCotangent ⟨b - algebraMap k A (ε b), sub_algebraMap_counit_mem k A b⟩)
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_add ψ, hlin, hlin, ← LinearMap.map_add]
  congr 1
  rw [Ideal.toCotangent_eq]

  have key : (a * b - algebraMap k A (ε (a * b))) - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b)))
      = (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) := by
    rw [Bialgebra.counit_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  change ((a * b - algebraMap k A (ε (a * b))) - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b))) : A) ∈ (I k A) ^ 2
  rw [key, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem k A a) (sub_algebraMap_counit_mem k A b)

private scoped instance finite_cotangent : Module.Finite k (cotangentSpace k A) := by
  haveI : IsNoetherian k A := IsNoetherian.iff_fg.2 inferInstance
  haveI : Module.Finite k ↥(I k A) := Module.IsNoetherian.finite k _
  exact Module.Finite.of_surjective (((I k A).toCotangent).restrictScalars k) (I k A).toCotangent_surjective

private noncomputable def primEquiv : ↥(primitives k (CartierDual k A)) ≃ₗ[k] Module.Dual k (cotangentSpace k A) where
  toFun φ := toCotDual k A φ.2
  map_add' φ ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [LinearMap.add_apply, toCotDual_toCotangent, toCotDual_toCotangent, toCotDual_toCotangent]
    rfl
  map_smul' c φ := by
    apply LinearMap.ext; intro d
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective d
    rw [RingHom.id_apply, LinearMap.smul_apply, toCotDual_toCotangent, toCotDual_toCotangent]
    rfl
  invFun ψ := ⟨CartierDual.ofDual k A (ofCotDualFun k A ψ), ofCotDualFun_mem k A ψ⟩
  left_inv φ := by
    apply Subtype.ext
    apply CartierDual.ext
    intro a
    change ofCotDualFun k A (toCotDual k A φ.2) a = φ.1 a
    change toCotDual k A φ.2 ((I k A).toCotangent ⟨a - algebraMap k A (ε a), _⟩) = φ.1 a
    rw [toCotDual_toCotangent]
    change φ.1 (a - algebraMap k A (ε a)) = φ.1 a
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, apply_one_eq_zero φ.2, smul_zero, sub_zero]
  right_inv ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [toCotDual_toCotangent]
    change ofCotDualFun k A ψ x = ψ ((I k A).toCotangent x)
    change ψ ((I k A).toCotangent ⟨(x : A) - algebraMap k A (ε x), _⟩) = ψ ((I k A).toCotangent x)
    congr 2
    apply Subtype.ext
    change (x : A) - algebraMap k A (ε x) = x
    rw [(mem_I k A).1 x.2, map_zero, sub_zero]

end PRIMCOUNT
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual.PRIMCOUNT"

namespace L2OP

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]

omit [Coalgebra.IsCocomm k B] [Module.Finite k B] in
private theorem mem_primitives_iff_comul (b : B) :
    b ∈ primitives k B ↔ Coalgebra.comul (R := k) b = b ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] b := by
  change b ∈ LinearMap.ker _ ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub]
  exact ⟨fun h => sub_eq_zero.mp h, fun h => sub_eq_zero.mpr h⟩

omit [Module.Finite k B] in

private theorem mul_pairing (ξ η : CartierDual k B) (b : B) :
    (ξ * η) b = TensorProduct.dualDistrib k B B (CartierDual.toDual k B ξ ⊗ₜ[k] CartierDual.toDual k B η)
      (Coalgebra.comul b) := CartierDual.mul_apply ξ η b

private theorem mem_primitives_iff_pairing (b : B) :
    b ∈ primitives k B ↔ ∀ ξ η : CartierDual k B, (ξ * η) b = ξ b * η 1 + ξ 1 * η b := by
  rw [mem_primitives_iff_comul]
  constructor
  · intro h ξ η
    rw [mul_pairing, h, map_add, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
    rfl
  · intro h

    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro Φ
    obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k B B).surjective Φ
    rw [CartierDual.dualDistribEquiv_apply_eq]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | tmul f g =>
      have := h (CartierDual.ofDual k B f) (CartierDual.ofDual k B g)
      rw [mul_pairing, CartierDual.toDual_ofDual, CartierDual.toDual_ofDual, CartierDual.ofDual_apply,
        CartierDual.ofDual_apply, CartierDual.ofDual_apply, CartierDual.ofDual_apply] at this
      rw [map_sub, this, map_add, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply, sub_self]

private noncomputable def E : B ≃ₗ[k] CartierDual k (CartierDual k B) :=
  (Module.evalEquiv k B).trans (((CartierDual.toDual k B).dualMap).trans (CartierDual.ofDual k (CartierDual k B)))

private theorem E_apply (b : B) (θ : CartierDual k B) : E k B b θ = θ b := rfl

private theorem map_primitives_E :
    (primitives k B).map (E k B).toLinearMap = primitives k (CartierDual k (CartierDual k B)) := by
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    rw [PRIMCOUNT.mem_primitives_iff]
    intro ξ η
    rw [LinearEquiv.coe_coe, E_apply, E_apply, E_apply, CartierDual.counit_apply, CartierDual.counit_apply]
    exact (mem_primitives_iff_pairing k B b).mp hb ξ η
  · intro φ hφ
    refine ⟨(E k B).symm φ, ?_, (E k B).apply_symm_apply φ⟩
    rw [SetLike.mem_coe, mem_primitives_iff_pairing]
    intro ξ η
    have := (PRIMCOUNT.mem_primitives_iff k (CartierDual k B) φ).mp hφ ξ η
    rw [CartierDual.counit_apply, CartierDual.counit_apply] at this
    rw [← E_apply k B ((E k B).symm φ), ← E_apply k B ((E k B).symm φ) ξ, ← E_apply k B ((E k B).symm φ) η,
      LinearEquiv.apply_symm_apply]
    exact this

private noncomputable abbrev ID : Ideal (CartierDual k B) := RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B))

private noncomputable def π : ↥(primitives k B) ≃ₗ[k] Module.Dual k (cotangentSpace k (CartierDual k B)) :=
  ((E k B).submoduleMap (primitives k B)).trans
    ((LinearEquiv.ofEq _ _ (map_primitives_E k B)).trans (PRIMCOUNT.primEquiv k (CartierDual k B)))

private theorem primEquiv_apply_toCotangent (φ : ↥(primitives k (CartierDual k (CartierDual k B)))) (x : ↥(ID k B)) :
    PRIMCOUNT.primEquiv k (CartierDual k B) φ ((ID k B).toCotangent x) = (φ : CartierDual k (CartierDual k B)) x :=
  PRIMCOUNT.toCotDual_toCotangent k (CartierDual k B) φ.2 x

private theorem π_apply_toCotangent (b : ↥(primitives k B)) (x : ↥(ID k B)) :
    π k B b ((ID k B).toCotangent x) = (x : CartierDual k B) b := by
  simp only [π, LinearEquiv.trans_apply]
  rw [primEquiv_apply_toCotangent]
  rfl

omit [Coalgebra.IsCocomm k B] [Module.Finite k B] in

private theorem map_mem_primitives (ψ : B →ₐc[k] B) {b : B} (hb : b ∈ primitives k B) : ψ b ∈ primitives k B := by
  rw [mem_primitives_iff_comul] at hb ⊢
  have h1 := LinearMap.congr_fun (CoalgHomClass.map_comp_comul (ψ : B →ₐc[k] B)) b
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
  rw [hb, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul] at h1
  simpa using h1.symm

private noncomputable def fP (ψ : B →ₐc[k] B) : ↥(primitives k B) →ₗ[k] ↥(primitives k B) :=
  ψ.toLinearMap.restrict fun _ hb => map_mem_primitives k B ψ hb

omit [Coalgebra.IsCocomm k B] [Module.Finite k B] in
private theorem fP_apply (ψ : B →ₐc[k] B) (b : ↥(primitives k B)) : (fP k B ψ b : B) = ψ b := rfl

private theorem π_fP (ψ : B →ₐc[k] B)
    (hI : ID k B ≤ (ID k B).comap (CartierDual.map ψ : CartierDual k B →ₐ[k] CartierDual k B))
    (b : ↥(primitives k B)) :
    π k B (fP k B ψ b) =
      (Ideal.mapCotangent (ID k B) (ID k B) (CartierDual.map ψ : CartierDual k B →ₐ[k] CartierDual k B) hI).dualMap
        (π k B b) := by
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := (ID k B).toCotangent_surjective c
  rw [π_apply_toCotangent, LinearMap.dualMap_apply, Ideal.mapCotangent_toCotangent, π_apply_toCotangent, fP_apply]
  rfl

private theorem finrank_quot_eq {ι : Type*} (ψ : ι → (B →ₐc[k] B))
    (hI : ∀ i, ID k B ≤ (ID k B).comap (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B)) :
    Module.finrank k (↥(primitives k B) ⧸
        ⨆ i, ((primitives k B).map (ψ i).toLinearMap).comap (primitives k B).subtype)
      = Module.finrank k ↥(⨅ i, LinearMap.ker
          (Ideal.mapCotangent (ID k B) (ID k B)
            (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i))) := by

  set P := primitives k B
  set g : ι → (cotangentSpace k (CartierDual k B) →ₗ[k] cotangentSpace k (CartierDual k B)) :=
    fun i => Ideal.mapCotangent (ID k B) (ID k B) (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i)
    with hg
  set S : Submodule k ↥P := ⨆ i, (P.map (ψ i).toLinearMap).comap P.subtype with hS
  set T : Submodule k (Module.Dual k (cotangentSpace k (CartierDual k B))) := ⨆ i, LinearMap.range (g i).dualMap with hT

  have hSi : ∀ i, (P.map (ψ i).toLinearMap).comap P.subtype = LinearMap.range (fP k B (ψ i)) := by
    intro i
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩

  have hπf : ∀ i, (π k B).toLinearMap ∘ₗ fP k B (ψ i) = (g i).dualMap ∘ₗ (π k B).toLinearMap := by
    intro i
    apply LinearMap.ext
    intro b
    exact π_fP k B (ψ i) (hI i) b
  have hST : S.map (π k B).toLinearMap = T := by
    rw [hS, Submodule.map_iSup]
    refine iSup_congr fun i => ?_
    rw [hSi, ← LinearMap.range_comp, hπf, LinearMap.range_comp_of_range_eq_top _ (π k B).range]

  rw [(Submodule.Quotient.equiv S T (π k B) hST).finrank_eq]

  have hTco : T.dualCoannihilator = ⨅ i, LinearMap.ker (g i) := by
    ext w
    rw [Submodule.mem_dualCoannihilator, Submodule.mem_iInf]
    constructor
    · intro h i
      rw [LinearMap.mem_ker]
      apply (Module.forall_dual_apply_eq_zero_iff k _).mp
      intro lam
      have := h ((g i).dualMap lam) (Submodule.mem_iSup_of_mem i ⟨lam, rfl⟩)
      rwa [LinearMap.dualMap_apply] at this
    · intro h φ hφ
      have hle : T ≤ LinearMap.ker (Module.Dual.eval k _ w) := by
        rw [hT]
        refine iSup_le fun i => ?_
        rintro _ ⟨lam, rfl⟩
        rw [LinearMap.mem_ker, Module.Dual.eval_apply, LinearMap.dualMap_apply, LinearMap.mem_ker.mp (h i), map_zero]
      have := hle hφ
      rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at this

  have h1 := Submodule.finrank_quotient_add_finrank T
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq T
  rw [Subspace.dual_finrank_eq] at h1
  rw [hTco] at h2
  have h3 : Module.finrank k ↥(⨅ i, LinearMap.ker (g i)) = Module.finrank k ↥(⨅ i, LinearMap.ker
      (Ideal.mapCotangent (ID k B) (ID k B)
        (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i))) := rfl
  omega

end L2OP
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual.PRIMCOUNT"

theorem solution
    (k : Type) [Field k] (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Module.Finite k B] {ι : Type} (ψ : ι → (B →ₐc[k] B))
    (hI : ∀ i, RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)) ≤
      (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B))).comap
        (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B)) :
    Module.finrank k (↥(primitives k B) ⧸
        ⨆ i, ((primitives k B).map (ψ i).toLinearMap).comap (primitives k B).subtype)
      = Module.finrank k ↥(⨅ i, LinearMap.ker
          (Ideal.mapCotangent (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i))) := by
  exact L2OP.finrank_quot_eq k B ψ hI

end S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual (solution)
