-- Prove2me | solution 1 for Ideal.exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/74222911-d716-5098-a2b1-15614cf38fe1

import Mathlib
import Theorems.Thm_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
import Theorems.Thm_CharacterModule_natCard_eq_of_finite
import Theorems.Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced

open scoped TensorProduct

noncomputable section

namespace P2MGorDefect

open Module

section IntegralForm

variable (B : Type*) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B]

abbrev jQ : B →ₐ[ℤ] ℚ ⊗[ℤ] B := Algebra.TensorProduct.includeRight

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem jQ_apply (b : B) : jQ B b = (1 : ℚ) ⊗ₜ[ℤ] b := rfl

omit [Module.Finite ℤ B] in
theorem jQ_injective : Function.Injective (jQ B) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem isReduced_tensor [IsReduced B] : IsReduced (ℚ ⊗[ℤ] B) := by
  letI : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) :=
    IsLocalization.tensorRight _ _
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ))
    (ℚ ⊗[ℤ] B) (inferInstance : IsReduced B)

theorem exists_ratForm [IsReduced B] :
    ∃ l : B →ₗ[ℤ] ℚ, ∀ x : B, (∀ y : B, l (x * y) = 0) → x = 0 := by
  haveI := isReduced_tensor B
  obtain ⟨l, hl⟩ := Algebra.exists_linearMap_apply_mul_eq_zero_imp_of_isReduced ℚ (ℚ ⊗[ℤ] B)
  refine ⟨(l.restrictScalars ℤ).comp (jQ B).toLinearMap, fun x hx => ?_⟩
  apply jQ_injective B
  rw [map_zero]
  apply hl
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero]
  | tmul q b =>
    have hqb : q ⊗ₜ[ℤ] b = q • ((1 : ℚ) ⊗ₜ[ℤ] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : jQ B x * ((1 : ℚ) ⊗ₜ[ℤ] b) = jQ B (x * b) := by rw [map_mul]; rfl
    rw [hqb, mul_smul_comm, map_smul, smul_eq_mul, e]
    have h : l (jQ B (x * b)) = 0 := hx b
    rw [h, mul_zero]
  | add z z' hz hz' => rw [mul_add, map_add, hz, hz', add_zero]

theorem exists_int_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℚ) :
    ∃ (D : ℕ) (z : ι → ℤ), D ≠ 0 ∧ ∀ i, (z i : ℚ) = (D : ℚ) * v i := by
  refine ⟨∏ i, (v i).den, fun i => (∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ)) * (v i).num,
    Finset.prod_ne_zero_iff.mpr fun i _ => (v i).den_ne_zero, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ (fun j => (v j).den) (Finset.mem_univ i)]
  push_cast
  rw [mul_assoc, Rat.den_mul_eq_num]

theorem exists_intForm [IsReduced B] :
    ∃ l : B →ₗ[ℤ] ℤ, ∀ x : B, (∀ y : B, l (x * y) = 0) → x = 0 := by
  classical
  obtain ⟨l, hl⟩ := exists_ratForm B
  let b := Module.finBasis ℤ B
  obtain ⟨D, z, hD, hz⟩ := exists_int_eq_mul (fun i => l (b i))
  let l₀ : B →ₗ[ℤ] ℤ := b.constr ℤ z
  have hcomp : (Int.castAddHom ℚ).toIntLinearMap.comp l₀ = (D : ℤ) • l := by
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom, LinearMap.smul_apply, l₀, Module.Basis.constr_basis]
    rw [hz i, zsmul_eq_mul, Int.cast_natCast]
  have hl₀ : ∀ x, (l₀ x : ℚ) = (D : ℚ) * l x := fun x => by
    have := LinearMap.congr_fun hcomp x
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_natCast] at this
    exact this
  refine ⟨l₀, fun x hx => hl x fun y => ?_⟩
  have h := hl₀ (x * y)
  rw [hx y, Int.cast_zero] at h
  rcases mul_eq_zero.mp h.symm with h' | h'
  · exact absurd h' (Nat.cast_ne_zero.mpr hD)
  · exact h'

end IntegralForm

section Gram

variable {B : Type*} [CommRing B] {r : ℕ} (b : Module.Basis (Fin r) ℤ B) (l₀ : B →ₗ[ℤ] ℤ)

def gram : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => l₀ (b i * b j)

theorem gram_apply (i j : Fin r) : gram b l₀ i j = l₀ (b i * b j) := rfl

theorem l₀_mul_basis (x : B) (j : Fin r) :
    l₀ (x * b j) = Matrix.vecMul (⇑(b.repr x)) (gram b l₀) j := by
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.sum_mul, map_sum]
  simp only [Matrix.vecMul, dotProduct, gram_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_zsmul, smul_eq_mul]

theorem l₀_mul (x y : B) :
    l₀ (x * y) = ∑ j, b.repr y j * Matrix.vecMul (⇑(b.repr x)) (gram b l₀) j := by
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_zsmul, l₀_mul_basis, smul_eq_mul]

variable (hl₀ : ∀ x : B, (∀ y : B, l₀ (x * y) = 0) → x = 0)
include hl₀

theorem det_gram_ne_zero : (gram b l₀).det ≠ 0 := by
  classical
  intro hdet
  have hdetT : (gram b l₀).transpose.det = 0 := by rw [Matrix.det_transpose, hdet]
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  rw [Matrix.mulVec_transpose] at hMv
  set x : B := b.equivFun.symm v with hxdef
  have hx : ⇑(b.repr x) = v := by
    have h1 : b.equivFun x = v := b.equivFun.apply_symm_apply v
    rw [← h1]
    rfl
  have hx0 : x = 0 := hl₀ x fun y => by
    rw [l₀_mul, hx, hMv]
    simp
  apply hv
  rw [← hx, hx0, map_zero]
  rfl

omit hl₀ in

theorem natAbs_det_mul_mem (n : ℕ) (z : B) (hz : ∀ y : B, (n : ℤ) ∣ l₀ (z * y)) :
    ((gram b l₀).det.natAbs : B) * z ∈ Ideal.span {(n : B)} := by
  classical
  set c : Fin r → ℤ := ⇑(b.repr z) with hc
  have h1 : ∀ j, (n : ℤ) ∣ Matrix.vecMul c (gram b l₀) j := fun j => by
    rw [hc, ← l₀_mul_basis]; exact hz (b j)
  have h2 : Matrix.vecMul (Matrix.vecMul c (gram b l₀)) (gram b l₀).adjugate =
      (gram b l₀).det • c := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  have h3 : ∀ i, (n : ℤ) ∣ (gram b l₀).det * c i := fun i => by
    have := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.dvd_sum fun j _ => (h1 j).mul_right _
  have h4 : ((gram b l₀).det : B) * z = ∑ i, ((gram b l₀).det * c i) • b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, smul_smul]
  have hmem : ((gram b l₀).det : B) * z ∈ Ideal.span {(n : B)} := by
    rw [h4]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := h3 i
    rw [hk, ← smul_smul, zsmul_eq_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rcases Int.natAbs_eq (gram b l₀).det with h | h
  · have : ((gram b l₀).det.natAbs : B) = ((gram b l₀).det : B) := by
      rw [← Int.cast_natCast, ← h]
    rw [this]; exact hmem
  · have h' : ((gram b l₀).det.natAbs : ℤ) = -(gram b l₀).det := by omega
    have : ((gram b l₀).det.natAbs : B) = -((gram b l₀).det : B) := by
      rw [← Int.cast_natCast, h', Int.cast_neg]
    rw [this, neg_mul]; exact Submodule.neg_mem _ hmem

end Gram

section Count

variable (B : Type*) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B]

omit [Module.Free ℤ B] in

theorem finite_quotient_span (n : ℕ) (hn : n ≠ 0) : Finite (B ⧸ Ideal.span {(n : B)}) := by
  haveI : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp inferInstance
  haveI : AddGroup.FG (B ⧸ Ideal.span {(n : B)}) :=
    AddGroup.fg_of_surjective (f := (Ideal.Quotient.mk (Ideal.span {(n : B)})).toAddMonoidHom)
      Ideal.Quotient.mk_surjective
  have htors : AddMonoid.IsTorsion (B ⧸ Ideal.span {(n : B)}) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
    rw [← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  exact AddCommGroup.finite_of_fg_torsion _ htors

variable (l₀ : B →ₗ[ℤ] ℤ) (e : ℕ)
  (hkey : ∀ (n : ℕ) (z : B), (∀ y : B, (n : ℤ) ∣ l₀ (z * y)) →
    (e : B) * z ∈ Ideal.span {(n : B)})
variable (n : ℕ) (J : Ideal B)

abbrev N₀ : AddSubgroup B := (Ideal.span {(n : B)}).toAddSubgroup

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem mem_N₀ {x : B} : x ∈ N₀ B n ↔ ∃ a : B, a * n = x := by
  change x ∈ Ideal.span {(n : B)} ↔ _
  exact Ideal.mem_span_singleton'

def P : AddSubgroup B where
  carrier := {x | ∀ j ∈ J, (n : ℤ) ∣ l₀ (x * j)}
  zero_mem' := fun j _ => by simp
  add_mem' := fun {x y} hx hy j hj => by
    simp only [add_mul, map_add]
    exact (hx j hj).add (hy j hj)
  neg_mem' := fun {x} hx j hj => by
    simp only [neg_mul, map_neg]
    exact (hx j hj).neg_right

def Q : AddSubgroup B where
  carrier := {x | ∀ j ∈ J, j * x ∈ Ideal.span {(n : B)}}
  zero_mem' := fun j _ => by simp
  add_mem' := fun {x y} hx hy j hj => by
    simp only [mul_add]
    exact Ideal.add_mem _ (hx j hj) (hy j hj)
  neg_mem' := fun {x} hx j hj => by
    simp only [mul_neg]
    exact Submodule.neg_mem _ (hx j hj)

def E : AddSubgroup B where
  carrier := {x | (e : B) * x ∈ Ideal.span {(n : B)}}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, mul_add]
    exact Ideal.add_mem _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, mul_neg]
    exact Submodule.neg_mem _ hx

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem mem_P {x : B} : x ∈ P B l₀ n J ↔ ∀ j ∈ J, (n : ℤ) ∣ l₀ (x * j) := Iff.rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem mem_Q {x : B} : x ∈ Q B n J ↔ ∀ j ∈ J, j * x ∈ Ideal.span {(n : B)} := Iff.rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem mem_E {x : B} : x ∈ E B e n ↔ (e : B) * x ∈ Ideal.span {(n : B)} := Iff.rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem N₀_le_P : N₀ B n ≤ P B l₀ n J := by
  intro x hx
  rw [mem_P]
  intro j _
  obtain ⟨a, rfl⟩ := (mem_N₀ B n).mp hx
  refine ⟨l₀ (a * j), ?_⟩
  have : a * (n : B) * j = (n : ℤ) • (a * j) := by
    rw [zsmul_eq_mul, Int.cast_natCast]; ring
  rw [this, map_zsmul, smul_eq_mul]

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem N₀_le_Q : N₀ B n ≤ Q B n J := by
  intro x hx
  rw [mem_Q]
  intro j _
  exact Ideal.mul_mem_left _ _ hx

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem N₀_le_E : N₀ B n ≤ E B e n := by
  intro x hx
  rw [mem_E]
  exact Ideal.mul_mem_left _ _ hx

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem N₀_le_J (hnJ : (n : B) ∈ J) : N₀ B n ≤ J.toAddSubgroup := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_N₀ B n).mp hx
  exact J.mul_mem_left a hnJ

variable (hn : n ≠ 0)
include hn

omit [Module.Free ℤ B] in
theorem index_N₀_ne_zero : (N₀ B n).index ≠ 0 := by
  haveI := finite_quotient_span B n hn
  have : (N₀ B n).index = Nat.card (B ⧸ Ideal.span {(n : B)}) := rfl
  rw [this]
  exact Nat.card_pos.ne'

omit [Module.Free ℤ B] in
theorem relIndex_N₀_ne_zero {K : AddSubgroup B} (hK : N₀ B n ≤ K) : (N₀ B n).relIndex K ≠ 0 := by
  intro h
  apply index_N₀_ne_zero B n hn
  rw [← AddSubgroup.relIndex_mul_index hK, h, zero_mul]

omit hn in

def toCirc : ℤ →+ AddCircle (1 : ℚ) where
  toFun k := (((k : ℚ) / n : ℚ) : AddCircle (1 : ℚ))
  map_zero' := by simp
  map_add' k k' := by
    push_cast
    rw [add_div]
    rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem toCirc_eq_zero_iff (k : ℤ) : toCirc n k = 0 ↔ (n : ℤ) ∣ k := by
  change (((k : ℚ) / n : ℚ) : AddCircle (1 : ℚ)) = 0 ↔ _
  rw [AddCircle.coe_eq_zero_iff]
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  constructor
  · rintro ⟨m, hm⟩
    rw [zsmul_eq_mul, mul_one, eq_div_iff hn'] at hm
    refine ⟨m, ?_⟩
    have : (k : ℚ) = ((n * m : ℤ) : ℚ) := by push_cast; rw [mul_comm]; exact hm.symm
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [zsmul_eq_mul, mul_one]
    push_cast
    field_simp

omit hn in

def pairJ : B →+ (↥J.toAddSubgroup →+ AddCircle (1 : ℚ)) where
  toFun x :=
    { toFun := fun j => toCirc n (l₀ (x * j))
      map_zero' := by simp
      map_add' := fun j j' => by
        simp only [AddSubgroup.coe_add, mul_add, map_add] }
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp [add_mul]

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem pairJ_apply (x : B) (j : ↥J.toAddSubgroup) :
    pairJ B l₀ n J x j = toCirc n (l₀ (x * j)) := rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem ker_pairJ : (pairJ B l₀ n J).ker = P B l₀ n J := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_P]
  constructor
  · intro h j hj
    have := DFunLike.congr_fun h ⟨j, hj⟩
    rw [pairJ_apply, AddMonoidHom.zero_apply, toCirc_eq_zero_iff n hn] at this
    exact this
  · intro h
    ext ⟨j, hj⟩
    rw [pairJ_apply, AddMonoidHom.zero_apply, toCirc_eq_zero_iff n hn]
    exact h j hj

omit hn in

def H₀ : AddSubgroup (↥J.toAddSubgroup →+ AddCircle (1 : ℚ)) where
  carrier := {f | ∀ j : ↥J.toAddSubgroup, (j : B) ∈ N₀ B n → f j = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {f g} hf hg j hj => by
    rw [AddMonoidHom.add_apply, hf j hj, hg j hj, add_zero]
  neg_mem' := fun {f} hf j hj => by rw [AddMonoidHom.neg_apply, hf j hj, neg_zero]

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem range_pairJ_le : (pairJ B l₀ n J).range ≤ H₀ B n J := by
  rintro _ ⟨x, rfl⟩ j hj
  rw [pairJ_apply, toCirc_eq_zero_iff n hn]
  obtain ⟨a, ha⟩ := (mem_N₀ B n).mp hj
  refine ⟨l₀ (x * a), ?_⟩
  rw [← ha]
  have : x * (a * (n : B)) = (n : ℤ) • (x * a) := by
    rw [zsmul_eq_mul, Int.cast_natCast]; ring
  rw [this, map_zsmul, smul_eq_mul]

omit hn in

abbrev Jn : AddSubgroup ↥J.toAddSubgroup := (N₀ B n).addSubgroupOf J.toAddSubgroup

omit hn in

def descend (f : ↥(H₀ B n J)) : CharacterModule (↥J.toAddSubgroup ⧸ Jn B n J) :=
  QuotientAddGroup.lift (Jn B n J) (f : ↥J.toAddSubgroup →+ AddCircle (1 : ℚ))
    (fun j hj => f.2 j (AddSubgroup.mem_addSubgroupOf.mp hj))

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem descend_injective : Function.Injective (descend B n J) := by
  intro f g h
  apply Subtype.ext
  ext j
  have := DFunLike.congr_fun h (QuotientAddGroup.mk j)
  simp [descend] at this
  exact this

variable (hnJ : (n : B) ∈ J)
include hnJ

omit [Module.Free ℤ B] in
theorem finite_JmodN : Finite (↥J.toAddSubgroup ⧸ Jn B n J) := by
  have h : (Jn B n J).index ≠ 0 := relIndex_N₀_ne_zero B n hn (N₀_le_J B n J hnJ)
  haveI : (Jn B n J).FiniteIndex := ⟨h⟩
  exact AddSubgroup.finite_quotient_of_finiteIndex

omit [Module.Free ℤ B] in
theorem finite_char : Finite (CharacterModule (↥J.toAddSubgroup ⧸ Jn B n J)) := by
  haveI := finite_JmodN B n J hn hnJ
  apply Nat.finite_of_card_ne_zero
  rw [CharacterModule.natCard_eq_of_finite]
  exact Nat.card_pos.ne'

omit [Module.Free ℤ B] in

theorem index_J_le : J.toAddSubgroup.index ≤ (N₀ B n).relIndex (P B l₀ n J) := by
  haveI := finite_char B n J hn hnJ
  haveI := finite_JmodN B n J hn hnJ
  haveI : Finite ↥(H₀ B n J) := Finite.of_injective _ (descend_injective B n J)

  have h1 : (P B l₀ n J).index ≤ (N₀ B n).relIndex J.toAddSubgroup := by
    rw [← ker_pairJ B l₀ n J hn, AddSubgroup.index_ker]
    calc Nat.card ↥(pairJ B l₀ n J).range
        ≤ Nat.card ↥(H₀ B n J) := AddSubgroup.card_le_of_le (range_pairJ_le B l₀ n J hn)
      _ ≤ Nat.card (CharacterModule (↥J.toAddSubgroup ⧸ Jn B n J)) :=
          Nat.card_le_card_of_injective _ (descend_injective B n J)
      _ = Nat.card (↥J.toAddSubgroup ⧸ Jn B n J) := CharacterModule.natCard_eq_of_finite _
      _ = (N₀ B n).relIndex J.toAddSubgroup := (AddSubgroup.index_eq_card _).symm

  have hJ := AddSubgroup.relIndex_mul_index (N₀_le_J B n J hnJ)
  have hP := AddSubgroup.relIndex_mul_index (N₀_le_P B l₀ n J)
  have hne : (N₀ B n).relIndex J.toAddSubgroup ≠ 0 :=
    relIndex_N₀_ne_zero B n hn (N₀_le_J B n J hnJ)
  have key : (N₀ B n).relIndex J.toAddSubgroup * J.toAddSubgroup.index ≤
      (N₀ B n).relIndex J.toAddSubgroup * (N₀ B n).relIndex (P B l₀ n J) := by
    calc (N₀ B n).relIndex J.toAddSubgroup * J.toAddSubgroup.index
        = (N₀ B n).relIndex (P B l₀ n J) * (P B l₀ n J).index := by rw [hJ, hP]
      _ ≤ (N₀ B n).relIndex (P B l₀ n J) * (N₀ B n).relIndex J.toAddSubgroup :=
          Nat.mul_le_mul_left _ h1
      _ = (N₀ B n).relIndex J.toAddSubgroup * (N₀ B n).relIndex (P B l₀ n J) := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left key (Nat.pos_of_ne_zero hne)

omit hnJ

omit hn in

abbrev mkN : B →+ B ⧸ Ideal.span {(n : B)} :=
  (Ideal.Quotient.mk (Ideal.span {(n : B)})).toAddMonoidHom

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem ker_mkN : (mkN B n).ker = N₀ B n := by
  ext x
  rw [AddMonoidHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem

omit hn in

abbrev ψ : ↥(P B l₀ n J) →+ B ⧸ Ideal.span {(n : B)} :=
  (mkN B n).comp ((AddMonoidHom.mulLeft (e : B)).comp (P B l₀ n J).subtype)

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem ψ_apply (x : ↥(P B l₀ n J)) : ψ B l₀ e n J x = mkN B n ((e : B) * x) := rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem ker_ψ : (ψ B l₀ e n J).ker = ((E B e n) ⊓ P B l₀ n J).addSubgroupOf (P B l₀ n J) := by
  ext x
  rw [AddMonoidHom.mem_ker, ψ_apply, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf, mem_E]
  change (Ideal.Quotient.mk _ _ = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

include hkey in
omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem range_ψ_le : (ψ B l₀ e n J).range ≤ (Q B n J).map (mkN B n) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(e : B) * x, ?_, rfl⟩
  change (e : B) * (x : B) ∈ Q B n J
  rw [mem_Q]
  intro j hj
  have hz : ∀ y : B, (n : ℤ) ∣ l₀ ((x : B) * j * y) := fun y => by
    rw [mul_assoc]
    exact x.2 (j * y) (J.mul_mem_right y hj)
  have := hkey n ((x : B) * j) hz
  have e1 : j * ((e : B) * x) = (e : B) * ((x : B) * j) := by ring
  rw [e1]
  exact this

include hkey in
omit [Module.Free ℤ B] in
theorem relIndex_P_le :
    (N₀ B n).relIndex (P B l₀ n J) ≤ (N₀ B n).relIndex (E B e n) * (N₀ B n).relIndex (Q B n J) := by
  haveI := finite_quotient_span B n hn
  set N₀' : AddSubgroup ↥(P B l₀ n J) := (N₀ B n).addSubgroupOf (P B l₀ n J) with hN₀'
  have hle : N₀' ≤ (ψ B l₀ e n J).ker := by
    intro x hx
    rw [ker_ψ, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
    exact ⟨N₀_le_E B e n (AddSubgroup.mem_addSubgroupOf.mp hx), x.2⟩
  have h1 : (N₀ B n).relIndex (P B l₀ n J) =
      N₀'.relIndex (ψ B l₀ e n J).ker * (ψ B l₀ e n J).ker.index :=
    (AddSubgroup.relIndex_mul_index hle).symm
  have h2 : (ψ B l₀ e n J).ker.index ≤ (N₀ B n).relIndex (Q B n J) := by
    rw [AddSubgroup.index_ker, ← ker_mkN B n, AddSubgroup.relIndex_ker]
    exact AddSubgroup.card_le_of_le (range_ψ_le B l₀ e hkey n J)
  have h3 : N₀'.relIndex (ψ B l₀ e n J).ker ≤ (N₀ B n).relIndex (E B e n) := by
    rw [ker_ψ, hN₀', AddSubgroup.relIndex_addSubgroupOf inf_le_right]
    exact AddSubgroup.relIndex_le_of_le_right inf_le_left
      (relIndex_N₀_ne_zero B n hn (N₀_le_E B e n))
  rw [h1]
  exact Nat.mul_le_mul h3 h2

omit hn in

abbrev LQ : Submodule ℤ (ℚ ⊗[ℤ] B) := LinearMap.range (jQ B).toLinearMap

scoped instance : Module.Free ℤ ↥(LQ B) :=
  Module.Free.of_equiv (LinearEquiv.ofInjective (jQ B).toLinearMap (jQ_injective B))

scoped instance : Module.Finite ℤ ↥(LQ B) :=
  Module.Finite.equiv (LinearEquiv.ofInjective (jQ B).toLinearMap (jQ_injective B))

omit hn in

def θ : ↥(E B e n) →+ (ℚ ⊗[ℤ] B) ⧸ LQ B where
  toFun x := (LQ B).mkQ (((n : ℚ)⁻¹) • jQ B x)
  map_zero' := by simp
  map_add' x y := by
    simp only [AddSubgroup.coe_add, map_add, smul_add]

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem θ_apply (x : ↥(E B e n)) : θ B e n x = (LQ B).mkQ (((n : ℚ)⁻¹) • jQ B x) := rfl

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem jQ_mul_natCast (a : B) : jQ B (a * (n : B)) = (n : ℚ) • jQ B a := by
  rw [map_mul, map_natCast, mul_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

omit [Module.Finite ℤ B] in
theorem ker_θ_le : (θ B e n).ker ≤ (N₀ B n).addSubgroupOf (E B e n) := by
  intro x hx
  rw [AddMonoidHom.mem_ker, θ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨a, ha⟩ := hx
  rw [AddSubgroup.mem_addSubgroupOf, mem_N₀]
  refine ⟨a, jQ_injective B ?_⟩
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  change jQ B a = (n : ℚ)⁻¹ • jQ B (x : B) at ha
  rw [jQ_mul_natCast, ha, smul_inv_smul₀ hn']

omit [Module.Finite ℤ B] [Module.Free ℤ B] in
theorem range_θ_le :
    (θ B e n).range ≤ (Submodule.torsionBy ℤ ((ℚ ⊗[ℤ] B) ⧸ LQ B) (e : ℕ)).toAddSubgroup := by
  rintro _ ⟨x, rfl⟩
  change θ B e n x ∈ Submodule.torsionBy ℤ _ _
  rw [Submodule.mem_torsionBy_iff, θ_apply, Submodule.mkQ_apply]
  change Submodule.Quotient.mk (((e : ℕ) : ℤ) • ((n : ℚ)⁻¹ • jQ B (x : B))) =
    (0 : (ℚ ⊗[ℤ] B) ⧸ LQ B)
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
  refine ⟨a, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((e : ℕ) : ℤ) • ((n : ℚ)⁻¹ • jQ B (x : B)) = (n : ℚ)⁻¹ • jQ B ((e : B) * x) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← natCast_zsmul, smul_comm]
  change jQ B a = _
  rw [h1, ← ha, jQ_mul_natCast, inv_smul_smul₀ hn']

theorem relIndex_E_le (he : e ≠ 0) :
    (N₀ B n).relIndex (E B e n) ≤ e ^ Module.finrank ℤ ↥(LQ B) := by
  have hcard := Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := ℚ) (LQ B) e he
  haveI : Finite ↥(Submodule.torsionBy ℤ ((ℚ ⊗[ℤ] B) ⧸ LQ B) (e : ℕ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ he
  haveI : Finite ↥(θ B e n).range :=
    Finite.of_injective (fun y : ↥(θ B e n).range => (⟨y.1, range_θ_le B e n hn y.2⟩ :
      ↥(Submodule.torsionBy ℤ ((ℚ ⊗[ℤ] B) ⧸ LQ B) (e : ℕ)).toAddSubgroup))
      (fun a b h => by
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact h')
  have h1 : ((N₀ B n).addSubgroupOf (E B e n)).index ≤ (θ B e n).ker.index := by
    apply Nat.le_of_dvd
    · rw [AddSubgroup.index_ker]
      exact Nat.card_pos
    · exact AddSubgroup.index_dvd_of_le (ker_θ_le B e n hn)
  calc (N₀ B n).relIndex (E B e n) = ((N₀ B n).addSubgroupOf (E B e n)).index := rfl
    _ ≤ (θ B e n).ker.index := h1
    _ = Nat.card ↥(θ B e n).range := AddSubgroup.index_ker _
    _ ≤ Nat.card ↥(Submodule.torsionBy ℤ ((ℚ ⊗[ℤ] B) ⧸ LQ B) (e : ℕ)).toAddSubgroup :=
        AddSubgroup.card_le_of_le (range_θ_le B e n hn)
    _ = e ^ Module.finrank ℤ ↥(LQ B) := hcard

omit [Module.Finite ℤ B] [Module.Free ℤ B] hn in
theorem relIndex_Q_eq :
    (N₀ B n).relIndex (Q B n J) =
      Nat.card ↥(Submodule.torsionBySet B (B ⧸ Ideal.span {(n : B)}) (J : Set B)) := by
  rw [← ker_mkN B n, AddSubgroup.relIndex_ker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  change y ∈ AddSubgroup.map (mkN B n) (Q B n J) ↔ y ∈ Submodule.torsionBySet _ _ _
  rw [AddSubgroup.mem_map, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨a, ha⟩
    change Ideal.Quotient.mk _ (a * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hx a ha
  · intro hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨x, ?_, rfl⟩
    rw [mem_Q]
    intro a ha
    have := hy ⟨a, ha⟩
    change Ideal.Quotient.mk _ (a * x) = 0 at this
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this

end Count

theorem main (B : Type*) [CommRing B] [IsReduced B] [Module.Finite ℤ B] [Module.Free ℤ B] :
    ∃ c : ℕ, 0 < c ∧ ∀ (n : ℕ), n ≠ 0 → ∀ J : Ideal B, (n : B) ∈ J →
      Nat.card (B ⧸ J) ≤
        c * Nat.card ↥(Submodule.torsionBySet B (B ⧸ Ideal.span {(n : B)}) (J : Set B)) := by
  classical
  obtain ⟨l₀, hl₀⟩ := exists_intForm B
  let b := Module.finBasis ℤ B
  set e : ℕ := (gram b l₀).det.natAbs with he_def
  have he : e ≠ 0 := Int.natAbs_ne_zero.mpr (det_gram_ne_zero b l₀ hl₀)
  have hkey : ∀ (n : ℕ) (z : B), (∀ y : B, (n : ℤ) ∣ l₀ (z * y)) →
      (e : B) * z ∈ Ideal.span {(n : B)} := fun n z hz => natAbs_det_mul_mem b l₀ n z hz
  refine ⟨e ^ Module.finrank ℤ ↥(LQ B), pow_pos (Nat.pos_of_ne_zero he) _,
    fun n hn J hnJ => ?_⟩
  have hidx : Nat.card (B ⧸ J) = J.toAddSubgroup.index := rfl
  rw [hidx]
  calc J.toAddSubgroup.index ≤ (N₀ B n).relIndex (P B l₀ n J) := index_J_le B l₀ n J hn hnJ
    _ ≤ (N₀ B n).relIndex (E B e n) * (N₀ B n).relIndex (Q B n J) :=
        relIndex_P_le B l₀ e hkey n J hn
    _ ≤ e ^ Module.finrank ℤ ↥(LQ B) *
          Nat.card ↥(Submodule.torsionBySet B (B ⧸ Ideal.span {(n : B)}) (J : Set B)) := by
        rw [← relIndex_Q_eq B n J]
        exact Nat.mul_le_mul_right _ (relIndex_E_le B e n hn he)

end P2MGorDefect
p2m_reactivate "P2MW.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced.P2MGorDefect"

end
p2m_reactivate "P2MW.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced.P2MGorDefect"

theorem solution
    (B : Type*) [CommRing B] [IsReduced B] [Module.Finite ℤ B] [Module.Free ℤ B] :
    ∃ c : ℕ, 0 < c ∧ ∀ (n : ℕ), n ≠ 0 → ∀ J : Ideal B, (n : B) ∈ J →
      Nat.card (B ⧸ J) ≤
        c * Nat.card ↥(Submodule.torsionBySet B (B ⧸ Ideal.span {(n : B)}) (J : Set B)) :=
  P2MGorDefect.main B

end S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced
end P2MW
export P2MW.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced (solution)
