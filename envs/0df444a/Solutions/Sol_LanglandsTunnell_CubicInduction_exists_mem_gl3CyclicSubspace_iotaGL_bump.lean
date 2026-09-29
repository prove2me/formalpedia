-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a0dd1139-1d69-5857-b7f1-f870f8273877

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField Topology Filter

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Balls

private theorem isOpen_ball (m : ℕ) : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(m : ℤ))} := by
  obtain ⟨t, ht, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) v m
  rw [← hvt]
  exact NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht

private theorem isClosed_ball (m : ℕ) : IsClosed {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(m : ℤ))} := by
  obtain ⟨t, ht, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) v m
  rw [← hvt]
  exact NumberField.AdelicLevel.isClosed_setOf_valued_le v t ht

private theorem isCompact_ball (m : ℕ) :
    IsCompact {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(m : ℤ))} := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    simpa only [Subtype.range_coe_subtype, SetLike.setOf_mem_eq] using
      isCompact_range (continuous_subtype_val (p := (· ∈ v.adicCompletionIntegers ℚ)))
  refine hO.of_isClosed_subset (isClosed_ball v m) fun y hy => ?_
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hy.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem exists_ball_subset_of_mem_nhds_zero {s : Set (v.adicCompletion ℚ)}
    (hs : s ∈ 𝓝 (0 : v.adicCompletion ℚ)) :
    ∃ m : ℕ, {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(m : ℤ))} ⊆ s := by
  refine exists_subset_nhds_of_isCompact' (V := fun m : ℕ => {y : v.adicCompletion ℚ |
      Valued.v y ≤ WithZero.exp (-(m : ℤ))}) ?_ (isCompact_ball v) (isClosed_ball v) ?_
  · refine directed_of_isDirected_le fun i j hij y hy => ?_
    exact le_trans hy (WithZero.exp_le_exp.mpr (by omega))
  · intro x hx
    have hx0 : x = 0 := by
      by_contra h
      have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
      obtain ⟨m, hm⟩ := WithZero.exists_exp_neg_natCast_lt hvx
      exact (not_le.mpr hm) (Set.mem_iInter.mp hx m)
    rw [hx0]
    exact hs

private theorem exists_ball_subset_of_mem_nhds {s : Set (v.adicCompletion ℚ)} {x : v.adicCompletion ℚ}
    (hs : s ∈ 𝓝 x) :
    ∃ m : ℕ, ∀ y : v.adicCompletion ℚ, Valued.v (y - x) ≤ WithZero.exp (-(m : ℤ)) → y ∈ s := by
  have hc : Continuous fun y : v.adicCompletion ℚ => y + x := continuous_id.add continuous_const
  have hs0 : (fun y => y + x) ⁻¹' s ∈ 𝓝 (0 : v.adicCompletion ℚ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa only [zero_add] using hs)
  obtain ⟨m, hm⟩ := exists_ball_subset_of_mem_nhds_zero v hs0
  refine ⟨m, fun y hy => ?_⟩
  simpa only [Set.mem_preimage, sub_add_cancel] using hm hy

end Balls

section MatrixNhds

variable {n : Type} [Fintype n] [DecidableEq n]

private theorem exists_depth_of_mem_nhds_one {C : Set (Matrix n n (v.adicCompletion ℚ))}
    (hC : C ∈ 𝓝 (1 : Matrix n n (v.adicCompletion ℚ))) :
    ∃ m : ℕ, ∀ M : Matrix n n (v.adicCompletion ℚ),
      (∀ i j, Valued.v (M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) → M ∈ C := by

  have hC' : (show Set (n → n → v.adicCompletion ℚ) from C) ∈
      Filter.pi fun i : n => 𝓝 ((1 : Matrix n n (v.adicCompletion ℚ)) i) := by
    rw [← nhds_pi]
    exact hC
  rw [Filter.mem_pi] at hC'
  obtain ⟨I, -, t, ht, htC⟩ := hC'
  have hrow : ∀ i, ∃ m : ℕ, ∀ r : n → v.adicCompletion ℚ,
      (∀ j, Valued.v (r j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) → r ∈ t i := by
    intro i
    have hti := ht i
    rw [nhds_pi, Filter.mem_pi] at hti
    obtain ⟨J, -, u, hu, huT⟩ := hti
    choose m hm using fun j => exists_ball_subset_of_mem_nhds v (hu j)
    refine ⟨∑ j, m j, fun r hr => huT fun j _ => hm j (r j) ((hr j).trans ?_)⟩
    have h1 : m j ≤ ∑ j, m j := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact WithZero.exp_le_exp.mpr (by omega)
  choose m hm using hrow
  refine ⟨∑ i, m i, fun M hM => htC fun i _ => hm i (M i) fun j => (hM i j).trans ?_⟩
  have h1 : m i ≤ ∑ i, m i := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem isOpen_setOf_entry_sub_one_le (m : ℕ) :
    IsOpen {M : Matrix n n (v.adicCompletion ℚ) |
      ∀ i j, Valued.v (M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))} := by
  have h : {M : Matrix n n (v.adicCompletion ℚ) |
      ∀ i j, Valued.v (M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))} =
      ⋂ i, ⋂ j, (fun M : Matrix n n (v.adicCompletion ℚ) => M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ⁻¹'
        {y | Valued.v y ≤ WithZero.exp (-(m : ℤ))} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_ball v m).preimage ((continuous_id.matrix_elem i j).sub continuous_const)

end MatrixNhds

section Congruence

variable (n : Type) [Fintype n] [DecidableEq n]

private theorem valued_mul_sub_one_apply_le {A B : Matrix n n (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (he : e ≤ 1)
    (hA : ∀ i j, Valued.v (A i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ e)
    (hB : ∀ i j, Valued.v (B i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ e) (i j : n) :
    Valued.v ((A * B) i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ e := by
  have hid : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hij : (A * B) i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j =
      ∑ k, (A i k - (1 : Matrix n n _) i k) * (B k j - (1 : Matrix n n _) k j) +
        (A i j - (1 : Matrix n n _) i j) + (B i j - (1 : Matrix n n _) i j) := by
    have := congrFun (congrFun hid i) j
    simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply] using this
  rw [hij]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sum_le _ fun k _ => ?_) (hA i j)) (hB i j)
  rw [Valuation.map_mul]
  calc Valued.v (A i k - (1 : Matrix n n _) i k) * Valued.v (B k j - (1 : Matrix n n _) k j)
      ≤ e * e := mul_le_mul' (hA i k) (hB k j)
    _ ≤ e * 1 := mul_le_mul' le_rfl he
    _ = e := mul_one e

private def congruenceGL (m : ℕ) : Subgroup (GL n (v.adicCompletion ℚ)) where
  carrier := {k | (∀ i j, Valued.v ((k : Matrix n n (v.adicCompletion ℚ)) i j -
      (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) ∧
    (∀ i j, Valued.v (((k⁻¹ : GL n (v.adicCompletion ℚ)) : Matrix n n (v.adicCompletion ℚ)) i j -
      (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ)))}
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    have he : WithZero.exp (-(m : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul]
      exact valued_mul_sub_one_apply_le v n he ha hb i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact valued_mul_sub_one_apply_le v n he hb' ha' i j
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa only [inv_inv] using ha⟩

variable {n}

private theorem mem_congruenceGL_iff {m : ℕ} {k : GL n (v.adicCompletion ℚ)} :
    k ∈ congruenceGL v n m ↔
      (∀ i j, Valued.v ((k : Matrix n n (v.adicCompletion ℚ)) i j -
        (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) ∧
      (∀ i j, Valued.v (((k⁻¹ : GL n (v.adicCompletion ℚ)) : Matrix n n (v.adicCompletion ℚ)) i j -
        (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) :=
  Iff.rfl

private theorem congruenceGL_antitone {m m' : ℕ} (h : m ≤ m') : congruenceGL v n m' ≤ congruenceGL v n m := by
  rintro k ⟨hk, hk'⟩
  have hle : WithZero.exp (-(m' : ℤ)) ≤ WithZero.exp (-(m : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  exact ⟨fun i j => (hk i j).trans hle, fun i j => (hk' i j).trans hle⟩

private theorem isOpen_congruenceGL (m : ℕ) : IsOpen (congruenceGL v n m : Set (GL n (v.adicCompletion ℚ))) := by
  have h : (congruenceGL v n m : Set (GL n (v.adicCompletion ℚ))) =
      ((↑) : GL n (v.adicCompletion ℚ) → Matrix n n (v.adicCompletion ℚ)) ⁻¹'
          {M | ∀ i j, Valued.v (M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))} ∩
        (fun k : GL n (v.adicCompletion ℚ) => ((k⁻¹ : GL n (v.adicCompletion ℚ)) : Matrix n n _)) ⁻¹'
          {M | ∀ i j, Valued.v (M i j - (1 : Matrix n n (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))} := by
    ext k
    rfl
  rw [h]
  exact ((isOpen_setOf_entry_sub_one_le v m).preimage Units.continuous_val).inter
    ((isOpen_setOf_entry_sub_one_le v m).preimage Units.continuous_coe_inv)

private theorem isOpen_of_congruenceGL_le {U : Subgroup (GL n (v.adicCompletion ℚ))} {m : ℕ}
    (h : congruenceGL v n m ≤ U) :
    IsOpen (U : Set (GL n (v.adicCompletion ℚ))) :=
  Subgroup.isOpen_mono h (isOpen_congruenceGL v m)

private theorem exists_congruenceGL_le_of_isOpen (U : Subgroup (GL n (v.adicCompletion ℚ)))
    (hU : IsOpen (U : Set (GL n (v.adicCompletion ℚ)))) : ∃ m : ℕ, congruenceGL v n m ≤ U := by
  have h1 : (U : Set (GL n (v.adicCompletion ℚ))) ∈ 𝓝 (1 : GL n (v.adicCompletion ℚ)) := hU.mem_nhds U.one_mem
  rw [(Units.isInducing_embedProduct (M := Matrix n n (v.adicCompletion ℚ))).nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨O, hO, hOU⟩ := h1
  have hO' : O ∈ 𝓝 ((1 : Matrix n n (v.adicCompletion ℚ)), MulOpposite.op (1 : Matrix n n (v.adicCompletion ℚ))) := by
    simpa only [Units.embedProduct_apply, Units.val_one, inv_one] using hO
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hO'
  obtain ⟨A, hA, B, hB, hABO⟩ := hO'
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix n n (v.adicCompletion ℚ)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨m₁, hm₁⟩ := exists_depth_of_mem_nhds_one v hA
  obtain ⟨m₂, hm₂⟩ := exists_depth_of_mem_nhds_one v hB'
  refine ⟨m₁ + m₂, fun k hk => ?_⟩
  obtain ⟨hk₁, hk₂⟩ := (mem_congruenceGL_iff v).mp (congruenceGL_antitone v (Nat.le_add_right m₁ m₂) hk)
  obtain ⟨-, hk₂'⟩ := (mem_congruenceGL_iff v).mp (congruenceGL_antitone v (Nat.le_add_left m₂ m₁) hk)
  have hval : (k : Matrix n n (v.adicCompletion ℚ)) ∈ A := hm₁ _ hk₁
  have hinv : ((k⁻¹ : GL n (v.adicCompletion ℚ)) : Matrix n n (v.adicCompletion ℚ)) ∈ MulOpposite.op ⁻¹' B :=
    hm₂ _ hk₂'
  apply hOU
  rw [Set.mem_preimage, Units.embedProduct_apply]
  exact hABO (Set.mk_mem_prod hval hinv)

private theorem exists_congruenceGL_le_comap_conj (U : Subgroup (GL n (v.adicCompletion ℚ)))
    (hU : IsOpen (U : Set (GL n (v.adicCompletion ℚ)))) (g : GL n (v.adicCompletion ℚ)) :
    ∃ m : ℕ, ∀ k ∈ congruenceGL v n m, g⁻¹ * k * g ∈ U := by
  have hc : Continuous fun k : GL n (v.adicCompletion ℚ) => g⁻¹ * k * g :=
    (continuous_const.mul continuous_id).mul continuous_const
  obtain ⟨m, hm⟩ := exists_congruenceGL_le_of_isOpen v (U.comap (MulAut.conj g⁻¹).toMonoidHom) (by
    have h__af := hU.preimage hc
    simp only [Subgroup.coe_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h__af ⊢
    exact h__af)
  refine ⟨m, fun k hk => ?_⟩
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm hk

private theorem exists_congruenceGL_translate_invariant {X : Type*} (W : GL n (v.adicCompletion ℚ) → X)
    {U : Subgroup (GL n (v.adicCompletion ℚ))} (hU : IsOpen (U : Set (GL n (v.adicCompletion ℚ))))
    (hW : ∀ k ∈ U, ∀ g, W (g * k) = W g) (g₁ : GL n (v.adicCompletion ℚ)) :
    ∃ m : ℕ, ∀ k ∈ congruenceGL v n m, ∀ g, W (g * k * g₁) = W (g * g₁) := by
  obtain ⟨m, hm⟩ := exists_congruenceGL_le_comap_conj v U hU g₁
  refine ⟨m, fun k hk g => ?_⟩
  have h := hW _ (hm k hk) (g * g₁)
  calc W (g * k * g₁) = W (g * g₁ * (g₁⁻¹ * k * g₁)) := by group
    _ = W (g * g₁) := h

end Congruence

section Mixed

private def MixedPattern (M P : ℕ) (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  Valued.v (A 0 0 - 1) ≤ WithZero.exp (-(M : ℤ)) ∧ Valued.v (A 0 1) ≤ WithZero.exp (-(P : ℤ)) ∧
    Valued.v (A 1 0) ≤ WithZero.exp (-(P : ℤ)) ∧ Valued.v (A 1 1 - 1) ≤ WithZero.exp (-(P : ℤ))

private theorem mixedPattern_one (M P : ℕ) : MixedPattern v M P (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  simp [MixedPattern]

private theorem mixedPattern_mul {M P : ℕ} (hMP : M ≤ P) {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hA : MixedPattern v M P A) (hB : MixedPattern v M P B) : MixedPattern v M P (A * B) := by
  obtain ⟨a00, a01, a10, a11⟩ := hA
  obtain ⟨b00, b01, b10, b11⟩ := hB
  have hPM : WithZero.exp (-(P : ℤ)) ≤ WithZero.exp (-(M : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hP1 : WithZero.exp (-(P : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
  have hM1 : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)

  have smul : ∀ {x y : v.adicCompletion ℚ} {e f g : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ e → Valued.v y ≤ f → e ≤ 1 → f ≤ g → Valued.v (x * y) ≤ g := by
    intro x y e f g hx hy he hf
    rw [Valuation.map_mul]
    calc Valued.v x * Valued.v y ≤ e * f := mul_le_mul' hx hy
      _ ≤ 1 * f := mul_le_mul' he le_rfl
      _ = f := one_mul f
      _ ≤ g := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h : (A * B) 0 0 - 1 = (A 0 0 - 1) * (B 0 0 - 1) + (A 0 0 - 1) + (B 0 0 - 1) + A 0 1 * B 1 0 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ a00) b00) ?_
    · exact smul a00 b00 hM1 le_rfl
    · exact smul a01 b10 hP1 hPM
  ·
    have h : (A * B) 0 1 = (A 0 0 - 1) * B 0 1 + B 0 1 + A 0 1 * (B 1 1 - 1) + A 0 1 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ b01) ?_) a01
    · exact smul a00 b01 hM1 le_rfl
    · exact smul a01 b11 hP1 le_rfl
  ·
    have h : (A * B) 1 0 = A 1 0 * (B 0 0 - 1) + A 1 0 + (A 1 1 - 1) * B 1 0 + B 1 0 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ a10) ?_) b10
    · rw [mul_comm]; exact smul b00 a10 hM1 le_rfl
    · exact smul a11 b10 hP1 le_rfl
  ·
    have h : (A * B) 1 1 - 1 = A 1 0 * B 0 1 + (A 1 1 - 1) * (B 1 1 - 1) + (A 1 1 - 1) + (B 1 1 - 1) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) a11) b11
    · exact smul a10 b01 hP1 le_rfl
    · exact smul a11 b11 hP1 le_rfl

private def mixedCongruence (M P : ℕ) (hMP : M ≤ P) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) where
  carrier := {k | MixedPattern v M P (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
    MixedPattern v M P ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using mixedPattern_one v M P
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mixedPattern_mul v hMP ha hb
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact mixedPattern_mul v hMP hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa only [inv_inv] using ha⟩

private theorem mem_mixedCongruence_iff {M P : ℕ} {hMP : M ≤ P} {k : GL (Fin 2) (v.adicCompletion ℚ)} :
    k ∈ mixedCongruence v M P hMP ↔
      MixedPattern v M P (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
        MixedPattern v M P ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
  Iff.rfl

private theorem mixedPattern_of_forall_le {M P : ℕ} (hMP : M ≤ P) {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (h : ∀ i j, Valued.v (A i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(P : ℤ))) :
    MixedPattern v M P A := by
  have hPM : WithZero.exp (-(P : ℤ)) ≤ WithZero.exp (-(M : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  refine ⟨(le_of_eq_of_le (by simp) (h 0 0)).trans hPM, ?_, ?_, le_of_eq_of_le (by simp) (h 1 1)⟩
  · simpa using h 0 1
  · simpa using h 1 0

private theorem forall_le_of_mixedPattern {M P : ℕ} (hMP : M ≤ P) {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (h : MixedPattern v M P A) :
    ∀ i j, Valued.v (A i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hPM : WithZero.exp (-(P : ℤ)) ≤ WithZero.exp (-(M : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  obtain ⟨a00, a01, a10, a11⟩ := h
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using a00
  · simpa using a01.trans hPM
  · simpa using a10.trans hPM
  · simpa using a11.trans hPM

private theorem congruenceGL_le_mixedCongruence {M P : ℕ} (hMP : M ≤ P) :
    congruenceGL v (Fin 2) P ≤ mixedCongruence v M P hMP := by
  rintro k ⟨hk, hk'⟩
  exact ⟨mixedPattern_of_forall_le v hMP hk, mixedPattern_of_forall_le v hMP hk'⟩

private theorem mixedCongruence_le_congruenceGL {M P : ℕ} (hMP : M ≤ P) :
    mixedCongruence v M P hMP ≤ congruenceGL v (Fin 2) M := by
  rintro k ⟨hk, hk'⟩
  exact ⟨forall_le_of_mixedPattern v hMP hk, forall_le_of_mixedPattern v hMP hk'⟩

private theorem isOpen_mixedCongruence {M P : ℕ} (hMP : M ≤ P) :
    IsOpen (mixedCongruence v M P hMP : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
  isOpen_of_congruenceGL_le v (congruenceGL_le_mixedCongruence v hMP)

private theorem exists_forall_mixedCongruence_le (U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU : IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    ∃ m₀ : ℕ, ∀ M P : ℕ, ∀ hMP : M ≤ P, m₀ ≤ M → mixedCongruence v M P hMP ≤ U := by
  obtain ⟨m₀, hm₀⟩ := exists_congruenceGL_le_of_isOpen v U hU
  exact ⟨m₀, fun M P hMP hM => ((mixedCongruence_le_congruenceGL v hMP).trans (congruenceGL_antitone v hM)).trans hm₀⟩

end Mixed

end LanglandsTunnell.CubicInduction.Kirillov

end

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SpanFurniture

variable {F : Type*} [CommRing F] {R : Type*} [CommRing R]

private theorem gl3AmbientRightTranslate_one (W : GL (Fin 3) F → R) :
    gl3AmbientRightTranslate (R := R) (1 : GL (Fin 3) F) W = W := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, mul_one]

private theorem translate_mem_gl3CyclicSubspace (W : GL (Fin 3) F → R) (g : GL (Fin 3) F) :
    gl3AmbientRightTranslate (R := R) g W ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨g, rfl⟩

private theorem self_mem_gl3CyclicSubspace (W : GL (Fin 3) F → R) : W ∈ gl3CyclicSubspace W := by
  simpa only [gl3AmbientRightTranslate_one] using translate_mem_gl3CyclicSubspace W (1 : GL (Fin 3) F)

private theorem gl3CyclicSubspace_le_of_mem {W V : GL (Fin 3) F → R} (hV : V ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace V ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g hV

private theorem sum_smul_translate_mem_gl3CyclicSubspace {ι : Type*} (s : Finset ι) (c : ι → R)
    (t : ι → GL (Fin 3) F) {W V : GL (Fin 3) F → R} (hV : V ∈ gl3CyclicSubspace W) :
    (∑ i ∈ s, c i • gl3AmbientRightTranslate (R := R) (t i) V) ∈ gl3CyclicSubspace W :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c i) (gl3AmbientRightTranslate_mem_gl3CyclicSubspace W (t i) hV)

private theorem gl3CyclicSubspace_le_gl3PsiWhittakerFnSpace (ψ : AddChar F R) {W : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F R ψ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ g ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)

private theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace (ψ : AddChar F R) {W V : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (hV : V ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ V :=
  (mem_gl3PsiWhittakerFnSpace_iff ψ V).mp (gl3CyclicSubspace_le_gl3PsiWhittakerFnSpace ψ hW hV)

end SpanFurniture

section TwoByTwo

variable {F : Type*} [CommRing F]

private def lowerUnipotentGL2 (e : F) : GL (Fin 2) F where
  val := !![1, 0; e, 1]
  inv := !![1, 0; -e, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem coe_lowerUnipotentGL2 (e : F) :
    ((lowerUnipotentGL2 e : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; e, 1] := rfl

@[scoped simp] private theorem lowerUnipotentGL2_zero : lowerUnipotentGL2 (0 : F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2]

private theorem diagUnits2_mul_unipotentGL2 (a d : Fˣ) (y : F) :
    diagUnits2 a d * unipotentGL2 y =
      unipotentGL2 ((a : F) * ((d⁻¹ : Fˣ) : F) * y) * diagUnits2 a d := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentGL2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm]

private def conjugatedLower (e y : F) : GL (Fin 2) F :=
  unipotentGL2 (-y) * lowerUnipotentGL2 e * unipotentGL2 y

private theorem lowerUnipotentGL2_mul_unipotentGL2 (e y : F) :
    lowerUnipotentGL2 e * unipotentGL2 y =
      unipotentGL2 y * conjugatedLower e y := by
  unfold conjugatedLower
  rw [← mul_assoc, ← mul_assoc, ← unipotentGL2_add, add_neg_cancel,
    unipotentGL2_zero, one_mul]

private theorem coe_conjugatedLower (e y : F) :
    ((conjugatedLower e y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1 - y * e, -(y * y * e); e, 1 + y * e] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatedLower, lowerUnipotentGL2, unipotentGL2, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[scoped simp] private theorem conjugatedLower_zero_left (y : F) : conjugatedLower (0 : F) y = 1 := by
  unfold conjugatedLower
  rw [lowerUnipotentGL2_zero, mul_one, ← unipotentGL2_add, neg_add_cancel,
    unipotentGL2_zero]

private def antidiagGL2 : GL (Fin 2) F where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem coe_antidiagGL2 :
    ((antidiagGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

end TwoByTwo

section BigCell

variable {F : Type*} [Field F]

private theorem eq_unipotent_mul_diag_mul_lower (h : GL (Fin 2) F)
    (hd : (h : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    h = unipotentGL2 ((h : Matrix (Fin 2) (Fin 2) F) 0 1 / (h : Matrix (Fin 2) (Fin 2) F) 1 1) *
      diagUnits2 (Units.mk0 ((h : Matrix (Fin 2) (Fin 2) F).det / (h : Matrix (Fin 2) (Fin 2) F) 1 1)
          (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) hd))
        (Units.mk0 ((h : Matrix (Fin 2) (Fin 2) F) 1 1) hd) *
      lowerUnipotentGL2 ((h : Matrix (Fin 2) (Fin 2) F) 1 0 / (h : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentGL2, unipotentGL2, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.det_fin_two] <;> field_simp
  ring

private theorem entries_ne_zero_of_apply_one_one_eq_zero (h : GL (Fin 2) F)
    (hd : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) :
    (h : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∧ (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero h
  rw [Matrix.det_fin_two, hd, mul_zero, zero_sub, neg_ne_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

private theorem eq_unipotent_mul_diag_mul_antidiag (h : GL (Fin 2) F)
    (hd : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) :
    h = unipotentGL2 ((h : Matrix (Fin 2) (Fin 2) F) 0 0 / (h : Matrix (Fin 2) (Fin 2) F) 1 0) *
      diagUnits2 (Units.mk0 _ (entries_ne_zero_of_apply_one_one_eq_zero h hd).1)
        (Units.mk0 _ (entries_ne_zero_of_apply_one_one_eq_zero h hd).2) * antidiagGL2 := by
  have h10 := (entries_ne_zero_of_apply_one_one_eq_zero h hd).2
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiagGL2, unipotentGL2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd]
  field_simp

end BigCell

section RatioCut

variable {F : Type*} [CommRing F]

private def ratioCut (ψ : AddChar F ℂ) (c : F) (s : Finset F) (W : GL (Fin 3) F → ℂ) : GL (Fin 3) F → ℂ :=
  ∑ y ∈ s, ψ (-(c * y)) • gl3AmbientRightTranslate (R := ℂ) (iotaGL (unipotentGL2 y)) W

private theorem ratioCut_mem_gl3CyclicSubspace (ψ : AddChar F ℂ) (c : F) (s : Finset F)
    {W V : GL (Fin 3) F → ℂ} (hV : V ∈ gl3CyclicSubspace W) : ratioCut ψ c s V ∈ gl3CyclicSubspace W :=
  sum_smul_translate_mem_gl3CyclicSubspace s _ _ hV

private theorem ratioCut_apply (ψ : AddChar F ℂ) (c : F) (s : Finset F) (W : GL (Fin 3) F → ℂ) (g : GL (Fin 3) F) :
    ratioCut ψ c s W g = ∑ y ∈ s, ψ (-(c * y)) * W (g * iotaGL (unipotentGL2 y)) := by
  simp only [ratioCut, Finset.sum_apply, Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul]

private theorem apply_iotaGL_unipotentGL2_mul {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (x : F) (t : GL (Fin 2) F) : W (iotaGL (unipotentGL2 x * t)) = ψ x * W (iotaGL t) := by
  rw [map_mul, iotaGL_unipotentGL2, hW x 0 0, add_zero]

private theorem ratioCut_apply_iotaGL {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) (c : F) (s : Finset F) (x : F) (a d : Fˣ)
    (e : F) (he : iotaGL (lowerUnipotentGL2 e) ∈ S) (hs : ∀ y ∈ s, iotaGL (conjugatedLower e y) ∈ S) :
    ratioCut ψ c s W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) =
      (∑ y ∈ s, ψ (((a : F) * ((d⁻¹ : Fˣ) : F) - c) * y)) *
        W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) := by

  have hpoint : W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) =
      ψ x * W (iotaGL (diagUnits2 a d)) := by
    rw [map_mul, hS _ he, apply_iotaGL_unipotentGL2_mul hW]
  rw [ratioCut_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_

  have hmove : unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e *
      unipotentGL2 y =
        unipotentGL2 (x + (a : F) * ((d⁻¹ : Fˣ) : F) * y) * diagUnits2 a d * conjugatedLower e y := by
    rw [mul_assoc (unipotentGL2 x * diagUnits2 a d), lowerUnipotentGL2_mul_unipotentGL2,
      ← mul_assoc, mul_assoc (unipotentGL2 x), diagUnits2_mul_unipotentGL2, ← mul_assoc,
      ← unipotentGL2_add]
  rw [← map_mul, hmove, map_mul, hS _ (hs y hy), apply_iotaGL_unipotentGL2_mul hW, hpoint,
    AddChar.map_add_eq_mul]
  have harg : ψ (-(c * y)) * (ψ x * ψ ((a : F) * ((d⁻¹ : Fˣ) : F) * y)) =
      ψ (((a : F) * ((d⁻¹ : Fˣ) : F) - c) * y) * ψ x := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc ψ (-(c * y)) * (ψ x * ψ ((a : F) * ((d⁻¹ : Fˣ) : F) * y) * W (iotaGL (diagUnits2 a d)))
      = ψ (-(c * y)) * (ψ x * ψ ((a : F) * ((d⁻¹ : Fˣ) : F) * y)) * W (iotaGL (diagUnits2 a d)) := by ring
    _ = ψ (((a : F) * ((d⁻¹ : Fˣ) : F) - c) * y) * ψ x * W (iotaGL (diagUnits2 a d)) := by rw [harg]
    _ = ψ (((a : F) * ((d⁻¹ : Fˣ) : F) - c) * y) * (ψ x * W (iotaGL (diagUnits2 a d))) := by ring

private theorem ratioCut_apply_iotaGL_eq_of_lower {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) (c : F)
    (s : Finset F) (x : F) (a d : Fˣ) {e e' : F} (he : iotaGL (lowerUnipotentGL2 e) ∈ S)
    (he' : iotaGL (lowerUnipotentGL2 e') ∈ S) (hs : ∀ y ∈ s, iotaGL (conjugatedLower e y) ∈ S)
    (hs' : ∀ y ∈ s, iotaGL (conjugatedLower e' y) ∈ S) :
    ratioCut ψ c s W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) =
      ratioCut ψ c s W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e')) := by
  rw [ratioCut_apply_iotaGL hW hS c s x a d e he hs, ratioCut_apply_iotaGL hW hS c s x a d e' he' hs']
  congr 1
  have h₁ : W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) =
      W (iotaGL (unipotentGL2 x * diagUnits2 a d)) := by
    rw [map_mul]
    exact hS _ he _
  have h₂ : W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e')) =
      W (iotaGL (unipotentGL2 x * diagUnits2 a d)) := by
    rw [map_mul]
    exact hS _ he' _
  rw [h₁, h₂]

end RatioCut

section CellEntries

variable {F : Type*} [CommRing F]

private theorem unipotent_mul_diag_mul_apply_one_zero (x : F) (a d : Fˣ) (κ : GL (Fin 2) F) :
    ((unipotentGL2 x * diagUnits2 a d * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (d : F) * (κ : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotent_mul_diag_mul_apply_one_one (x : F) (a d : Fˣ) (κ : GL (Fin 2) F) :
    ((unipotentGL2 x * diagUnits2 a d * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (d : F) * (κ : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_unipotent_mul_diag_mul (x : F) (a d : Fˣ) (κ : GL (Fin 2) F) :
    ((unipotentGL2 x * diagUnits2 a d * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (a : F) * (d : F) * (κ : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_two_of]

private theorem diagUnits2_mul_diagUnits2 (a b c d : Fˣ) :
    diagUnits2 a b * diagUnits2 c d = diagUnits2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem coe_lowerUnipotentGL2_inv (e : F) :
    (((lowerUnipotentGL2 e)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -e, 1] :=
  rfl

@[scoped simp] private theorem coe_diagUnits2_inv (u w : Fˣ) :
    (((diagUnits2 u w)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((u⁻¹ : Fˣ) : F), 0; 0, ((w⁻¹ : Fˣ) : F)] :=
  rfl

private theorem lowerUnipotentGL2_inv (e : F) : (lowerUnipotentGL2 e)⁻¹ = lowerUnipotentGL2 (-e) :=
  Units.ext rfl

private theorem unipotentGL2_inv (y : F) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem conjugatedLower_inv (e y : F) : (conjugatedLower e y)⁻¹ = conjugatedLower (-e) y := by
  simp only [conjugatedLower, _root_.mul_inv_rev, lowerUnipotentGL2_inv, unipotentGL2_inv, neg_neg, mul_assoc]

private theorem conjugatedLower_zero_right (e : F) : conjugatedLower e 0 = lowerUnipotentGL2 e := by
  simp [conjugatedLower]

private theorem coe_diagUnits2_mul_lowerUnipotentGL2 (u w : Fˣ) (e : F) :
    ((diagUnits2 u w * lowerUnipotentGL2 e : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(u : F), 0; (w : F) * e, (w : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem coe_diagUnits2_mul_lowerUnipotentGL2_inv (u w : Fˣ) (e : F) :
    (((diagUnits2 u w * lowerUnipotentGL2 e)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((u⁻¹ : Fˣ) : F), 0; -e * ((u⁻¹ : Fˣ) : F), ((w⁻¹ : Fˣ) : F)] := by
  rw [_root_.mul_inv_rev, Units.val_mul, coe_lowerUnipotentGL2_inv, coe_diagUnits2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end CellEntries

section ValuedFurniture

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem exp_neg_natCast_le_one (k : ℕ) : WithZero.exp (-(k : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by omega)

private theorem exp_neg_natCast_le_of_le {a b : ℕ} (h : a ≤ b) : WithZero.exp (-(b : ℤ)) ≤ WithZero.exp (-(a : ℤ)) :=
  WithZero.exp_le_exp.mpr (by omega)

private theorem valued_mul_le_of_le_one {x y : v.adicCompletion ℚ} {e f : WithZero (Multiplicative ℤ)}
    (hx : Valued.v x ≤ e) (hy : Valued.v y ≤ f) (he : e ≤ 1) : Valued.v (x * y) ≤ f := by
  rw [Valuation.map_mul]
  calc Valued.v x * Valued.v y ≤ e * f := mul_le_mul' hx hy
    _ ≤ 1 * f := mul_le_mul' he le_rfl
    _ = f := one_mul f

private theorem valued_mul_le_exp_add {x y : v.adicCompletion ℚ} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

private theorem valued_eq_one_of_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (h : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < 1 := by
    refine lt_of_le_of_lt h ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h1 := Valuation.map_one_add_of_lt _ hlt
  rwa [add_sub_cancel] at h1

private theorem ne_zero_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (h : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : u ≠ 0 := by
  intro hu
  have h1 := valued_eq_one_of_sub_one_le hk h
  rw [hu, Valuation.map_zero] at h1
  exact zero_ne_one h1

private theorem valued_inv_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (h : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v (u⁻¹ - 1) ≤ WithZero.exp (-(k : ℤ)) := by
  have hu0 : u ≠ 0 := ne_zero_of_valued_sub_one_le hk h
  have hu1 : Valued.v u = 1 := valued_eq_one_of_sub_one_le hk h
  have heq : u⁻¹ - 1 = (1 - u) * u⁻¹ := by rw [sub_mul, one_mul, mul_inv_cancel₀ hu0]
  rw [heq, Valuation.map_mul, map_inv₀, hu1, inv_one, mul_one, Valuation.map_sub_swap]
  exact h

end ValuedFurniture

section CellGeometry

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def InCell (a₀ d₀ : (v.adicCompletion ℚ)ˣ) (M P : ℕ) (h : GL (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 / (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp (-(P : ℤ)) ∧
    Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1) ≤
      WithZero.exp (-(P : ℤ)) ∧
    Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
        ((a₀ : v.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) - 1) ≤
      WithZero.exp (-(M : ℤ))

variable {v}

private theorem mixedPattern_of_entries {M P : ℕ} {p q r s : v.adicCompletion ℚ}
    (h00 : Valued.v (p - 1) ≤ WithZero.exp (-(M : ℤ))) (h01 : Valued.v q ≤ WithZero.exp (-(P : ℤ)))
    (h10 : Valued.v r ≤ WithZero.exp (-(P : ℤ))) (h11 : Valued.v (s - 1) ≤ WithZero.exp (-(P : ℤ))) :
    MixedPattern v M P !![p, q; r, s] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa

private theorem valued_det_div_sub_one_le_of_mixedPattern {M P : ℕ} (hMP : M ≤ P) (hP : 1 ≤ P)
    {K : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hK : MixedPattern v M P K) :
    Valued.v (K.det / K 1 1 - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  obtain ⟨h00, h01, h10, h11⟩ := hK
  have hk : K 1 1 ≠ 0 := ne_zero_of_valued_sub_one_le hP h11
  have heq : K.det / K 1 1 - 1 = (K 0 0 - 1) - K 0 1 * K 1 0 / K 1 1 := by
    rw [Matrix.det_fin_two]
    field_simp
    ring
  rw [heq]
  refine Valuation.map_sub_le _ h00 ?_
  rw [map_div₀, valued_eq_one_of_sub_one_le hP h11, div_one]
  exact le_trans (valued_mul_le_of_le_one h01 h10 (exp_neg_natCast_le_one P)) (exp_neg_natCast_le_of_le hMP)

private theorem valued_det_div_sq_sub_one_le_of_mixedPattern {M P : ℕ} (hMP : M ≤ P) (hP : 1 ≤ P)
    {K : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hK : MixedPattern v M P K) :
    Valued.v (K.det / (K 1 1 * K 1 1) - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  obtain ⟨h00, h01, h10, h11⟩ := hK
  have hk : K 1 1 ≠ 0 := ne_zero_of_valued_sub_one_le hP h11
  have hk1 : Valued.v (K 1 1) = 1 := valued_eq_one_of_sub_one_le hP h11
  have heq : K.det / (K 1 1 * K 1 1) - 1 =
      ((K 0 0 - 1) - (K 1 1 - 1)) / K 1 1 - K 0 1 * K 1 0 / (K 1 1 * K 1 1) := by
    rw [Matrix.det_fin_two]
    field_simp
    ring
  rw [heq]
  refine Valuation.map_sub_le _ ?_ ?_
  · rw [map_div₀, hk1, div_one]
    exact Valuation.map_sub_le _ h00 (le_trans h11 (exp_neg_natCast_le_of_le hMP))
  · have hden : Valued.v (K 1 1 * K 1 1) = 1 := by rw [Valuation.map_mul, hk1, one_mul]
    rw [map_div₀, hden, div_one]
    exact le_trans (valued_mul_le_of_le_one h01 h10 (exp_neg_natCast_le_one P)) (exp_neg_natCast_le_of_le hMP)

private theorem inCell_of_mixedPattern (a₀ d₀ : (v.adicCompletion ℚ)ˣ) {M P : ℕ} (hMP : M ≤ P) (hP : 1 ≤ P)
    (x : v.adicCompletion ℚ) {κ : GL (Fin 2) (v.adicCompletion ℚ)}
    (hκ : MixedPattern v M P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    InCell v a₀ d₀ M P (unipotentGL2 x * diagUnits2 a₀ d₀ * κ) := by
  obtain ⟨-, -, h10, h11⟩ := id hκ
  have hd : (d₀ : v.adicCompletion ℚ) ≠ 0 := d₀.ne_zero
  have ha : (a₀ : v.adicCompletion ℚ) ≠ 0 := a₀.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [unipotent_mul_diag_mul_apply_one_zero, mul_div_cancel_left₀ _ hd]
    exact h10
  · rw [unipotent_mul_diag_mul_apply_one_one, mul_div_cancel_left₀ _ hd]
    exact h11
  · rw [det_unipotent_mul_diag_mul, unipotent_mul_diag_mul_apply_one_one, mul_assoc, mul_div_mul_left _ _ ha,
      mul_div_mul_left _ _ hd]
    exact valued_det_div_sub_one_le_of_mixedPattern hMP hP hκ

private theorem exists_mixedPattern_of_inCell (a₀ d₀ : (v.adicCompletion ℚ)ˣ) {M P : ℕ} (hM : 1 ≤ M) (hMP : M ≤ P)
    {h : GL (Fin 2) (v.adicCompletion ℚ)} (hh : InCell v a₀ d₀ M P h) :
    ∃ x : v.adicCompletion ℚ, ∃ κ : GL (Fin 2) (v.adicCompletion ℚ),
      MixedPattern v M P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
        MixedPattern v M P ((κ⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
          h = unipotentGL2 x * diagUnits2 a₀ d₀ * κ := by
  obtain ⟨c10, c11, c00⟩ := hh
  have hP : 1 ≤ P := le_trans hM hMP
  have hd : (d₀ : v.adicCompletion ℚ) ≠ 0 := d₀.ne_zero
  have hq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) ≠ 0 :=
    ne_zero_of_valued_sub_one_le hP c11
  have h11 : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := by
    intro h0
    exact hq (by rw [h0, zero_div])
  have hdet : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero h

  set u : (v.adicCompletion ℚ)ˣ := a₀⁻¹ * Units.mk0 _ (div_ne_zero hdet h11) with hu_def
  set w : (v.adicCompletion ℚ)ˣ := d₀⁻¹ * Units.mk0 _ h11 with hw_def
  set e : v.adicCompletion ℚ := (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
    (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 with he_def
  have hu : (u : v.adicCompletion ℚ) = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
      ((a₀ : v.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) := by
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    ring
  have hw : (w : v.adicCompletion ℚ) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) := by
    rw [hw_def, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    ring
  have hwe : (w : v.adicCompletion ℚ) * e =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 / (d₀ : v.adicCompletion ℚ) := by
    rw [hw, he_def]
    field_simp
  have H00 : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(M : ℤ)) := by rw [hu]; exact c00
  have H11 : Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(P : ℤ)) := by rw [hw]; exact c11
  have H10 : Valued.v ((w : v.adicCompletion ℚ) * e) ≤ WithZero.exp (-(P : ℤ)) := by rw [hwe]; exact c10
  have Hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 := valued_eq_one_of_sub_one_le hM H00
  have He : Valued.v e ≤ WithZero.exp (-(P : ℤ)) := by
    have hw0 : (w : v.adicCompletion ℚ) ≠ 0 := w.ne_zero
    have hw1 : Valued.v (w : v.adicCompletion ℚ) = 1 := valued_eq_one_of_sub_one_le hP H11
    have : e = (w : v.adicCompletion ℚ) * e / (w : v.adicCompletion ℚ) := by
      rw [mul_div_cancel_left₀ _ hw0]
    rw [this, map_div₀, hw1, div_one]
    exact H10
  refine ⟨(h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1, diagUnits2 u w * lowerUnipotentGL2 e, ?_, ?_, ?_⟩
  · rw [coe_diagUnits2_mul_lowerUnipotentGL2]
    exact mixedPattern_of_entries H00 (by simp) H10 H11
  · rw [coe_diagUnits2_mul_lowerUnipotentGL2_inv]
    refine mixedPattern_of_entries ?_ (by simp) ?_ ?_
    · rw [Units.val_inv_eq_inv_val]
      exact valued_inv_sub_one_le hM H00
    · rw [Valuation.map_mul, Valuation.map_neg, Units.val_inv_eq_inv_val, map_inv₀, Hu1, inv_one, mul_one]
      exact He
    · rw [Units.val_inv_eq_inv_val]
      exact valued_inv_sub_one_le hP H11
  · conv_lhs => rw [eq_unipotent_mul_diag_mul_lower h h11]
    rw [← mul_assoc, mul_assoc (unipotentGL2 _) (diagUnits2 a₀ d₀), diagUnits2_mul_diagUnits2, hu_def, hw_def,
      mul_inv_cancel_left, mul_inv_cancel_left]

private theorem inCell_iff (a₀ d₀ : (v.adicCompletion ℚ)ˣ) {M P : ℕ} (hM : 1 ≤ M) (hMP : M ≤ P)
    (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    InCell v a₀ d₀ M P h ↔ ∃ x : v.adicCompletion ℚ, ∃ κ : GL (Fin 2) (v.adicCompletion ℚ),
      (MixedPattern v M P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
        MixedPattern v M P ((κ⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
          h = unipotentGL2 x * diagUnits2 a₀ d₀ * κ := by
  constructor
  · intro hh
    obtain ⟨x, κ, hκ, hκ', rfl⟩ := exists_mixedPattern_of_inCell a₀ d₀ hM hMP hh
    exact ⟨x, κ, ⟨hκ, hκ'⟩, rfl⟩
  · rintro ⟨x, κ, ⟨hκ, -⟩, rfl⟩
    exact inCell_of_mixedPattern a₀ d₀ hMP (le_trans hM hMP) x hκ

end CellGeometry

section Margin

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem conjugatedLower_entries_sub_one_le {k M : ℕ} {e y : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) (hy : Valued.v y ≤ WithZero.exp (M : ℤ)) :
    ∀ i j, Valued.v ((conjugatedLower e y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  have hye : Valued.v (y * e) ≤ WithZero.exp (-(k : ℤ)) :=
    le_trans (valued_mul_le_exp_add hy he) (WithZero.exp_le_exp.mpr (by omega))
  have hyye : Valued.v (y * y * e) ≤ WithZero.exp (-(k : ℤ)) :=
    le_trans (valued_mul_le_exp_add (valued_mul_le_exp_add hy hy) he) (WithZero.exp_le_exp.mpr (by omega))
  have hek : Valued.v e ≤ WithZero.exp (-(k : ℤ)) := le_trans he (WithZero.exp_le_exp.mpr (by omega))
  intro i j
  rw [coe_conjugatedLower]
  fin_cases i <;> fin_cases j
  · simpa using hye
  · simpa using hyye
  · simpa using hek
  · simpa using hye

private theorem conjugatedLower_inv_entries_sub_one_le {k M : ℕ} {e y : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) (hy : Valued.v y ≤ WithZero.exp (M : ℤ)) :
    ∀ i j, Valued.v ((((conjugatedLower e y)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [conjugatedLower_inv]
  exact conjugatedLower_entries_sub_one_le (by rwa [Valuation.map_neg]) hy

private theorem embedMat2_entries_sub_one_le {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    {g : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ g) :
    ∀ i j, Valued.v (embedMat2 A i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ g := by
  have h00 : Valued.v (A 0 0 - 1) ≤ g := by simpa using hA 0 0
  have h01 : Valued.v (A 0 1) ≤ g := by simpa using hA 0 1
  have h10 : Valued.v (A 1 0) ≤ g := by simpa using hA 1 0
  have h11 : Valued.v (A 1 1 - 1) ≤ g := by simpa using hA 1 1
  intro i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, h00, h01, h10, h11]

private theorem iotaGL_conjugatedLower_entries_le {k M : ℕ} {e y : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) (hy : Valued.v y ≤ WithZero.exp (M : ℤ)) :
    (∀ i j, Valued.v (((iotaGL (conjugatedLower e y) : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) ∧
      (∀ i j, Valued.v ((((iotaGL (conjugatedLower e y))⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) := by
  refine ⟨?_, ?_⟩
  · rw [coe_iotaGL]
    exact embedMat2_entries_sub_one_le (conjugatedLower_entries_sub_one_le he hy)
  · rw [← map_inv, coe_iotaGL]
    exact embedMat2_entries_sub_one_le (conjugatedLower_inv_entries_sub_one_le he hy)

private theorem iotaGL_lowerUnipotentGL2_entries_le {k M : ℕ} {e : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) :
    (∀ i j, Valued.v (((iotaGL (lowerUnipotentGL2 e) : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) ∧
      (∀ i j, Valued.v ((((iotaGL (lowerUnipotentGL2 e))⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) := by
  rw [← conjugatedLower_zero_right e]
  exact iotaGL_conjugatedLower_entries_le (M := M) he (by simp)

private theorem diagUnits2_entries_sub_one_le {k : ℕ} {u w : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)))
    (hw : Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ))) :
    ∀ i j, Valued.v ((diagUnits2 u w : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  intro i j
  rw [coe_diagUnits2]
  fin_cases i <;> fin_cases j
  · simpa using hu
  · simp
  · simp
  · simpa using hw

private theorem diagUnits2_inv_entries_sub_one_le {k : ℕ} (hk : 1 ≤ k) {u w : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)))
    (hw : Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ))) :
    ∀ i j, Valued.v ((((diagUnits2 u w)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  have hu' : Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [Units.val_inv_eq_inv_val]
    exact valued_inv_sub_one_le hk hu
  have hw' : Valued.v (((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [Units.val_inv_eq_inv_val]
    exact valued_inv_sub_one_le hk hw
  intro i j
  rw [coe_diagUnits2_inv]
  fin_cases i <;> fin_cases j
  · simpa using hu'
  · simp
  · simp
  · simpa using hw'

private theorem iotaGL_diagUnits2_entries_le {k : ℕ} (hk : 1 ≤ k) {u w : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)))
    (hw : Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ))) :
    (∀ i j, Valued.v (((iotaGL (diagUnits2 u w) : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) ∧
      (∀ i j, Valued.v ((((iotaGL (diagUnits2 u w))⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k : ℤ))) := by
  refine ⟨?_, ?_⟩
  · rw [coe_iotaGL]
    exact embedMat2_entries_sub_one_le (diagUnits2_entries_sub_one_le hu hw)
  · rw [← map_inv, coe_iotaGL]
    exact embedMat2_entries_sub_one_le (diagUnits2_inv_entries_sub_one_le hk hu hw)

end Margin

section Bridge

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem valued_le_of_forall_addChar_mul_eq_one {ψ : AddChar (v.adicCompletion ℚ) ℂ} {ℓ : ℤ}
    {x₁ : v.adicCompletion ℚ} (hx₁ : Valued.v x₁ ≤ WithZero.exp (-(ℓ - 1))) (hψx₁ : ψ x₁ ≠ 1) {N : ℤ}
    {c : v.adicCompletion ℚ} (hc : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ WithZero.exp N → ψ (c * z) = 1) :
    Valued.v c ≤ WithZero.exp (-(ℓ + N)) := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_contra hcon
  rw [not_le] at hcon
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  have hexp : Valued.v c = WithZero.exp (WithZero.log (Valued.v c)) := (WithZero.exp_log hvc).symm
  rw [hexp, WithZero.exp_lt_exp] at hcon
  have hz : Valued.v (x₁ / c) ≤ WithZero.exp N := by
    rw [map_div₀, hexp, div_eq_mul_inv, ← WithZero.exp_neg]
    calc Valued.v x₁ * WithZero.exp (-WithZero.log (Valued.v c)) ≤
          WithZero.exp (-(ℓ - 1)) * WithZero.exp (-WithZero.log (Valued.v c)) := mul_le_mul' hx₁ le_rfl
      _ = WithZero.exp (-(ℓ - 1) + -WithZero.log (Valued.v c)) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp N := WithZero.exp_le_exp.mpr (by omega)
  have heq : c * (x₁ / c) = x₁ := by field_simp
  have h1 := hc (x₁ / c) hz
  rw [heq] at h1
  exact hψx₁ h1

private theorem valued_div_le_exp_sub_log {x d : v.adicCompletion ℚ} (hd : d ≠ 0) {a : ℤ}
    (hx : Valued.v x ≤ WithZero.exp a) :
    Valued.v (x / d) ≤ WithZero.exp (a - WithZero.log (Valued.v d)) := by
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).mpr hd
  rw [map_div₀, div_eq_mul_inv, sub_eq_add_neg, WithZero.exp_add, WithZero.exp_neg, WithZero.exp_log hvd]
  exact mul_le_mul' hx le_rfl

private theorem inCell_of_valued_entries (a₀ d₀ : (v.adicCompletion ℚ)ˣ) {M P : ℕ} (hM : 1 ≤ M) (hMP : M ≤ P)
    {α β : ℤ} (hPα : WithZero.exp (α - WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))) ≤ WithZero.exp (-(P : ℤ)))
    (hMβ : WithZero.exp (β - WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))) ≤
      WithZero.exp (-(M : ℤ)))
    {h : GL (Fin 2) (v.adicCompletion ℚ)}
    (h10 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ WithZero.exp α)
    (h11 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 - (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp α)
    (hratio : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) -
        (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)) ≤ WithZero.exp β) :
    InCell v a₀ d₀ M P h := by
  have hP : 1 ≤ P := le_trans hM hMP
  have hd : (d₀ : v.adicCompletion ℚ) ≠ 0 := d₀.ne_zero
  have ha : (a₀ : v.adicCompletion ℚ) ≠ 0 := a₀.ne_zero
  have hc : (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ) ≠ 0 := div_ne_zero ha hd

  have C10 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 / (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp (-(P : ℤ)) := le_trans (valued_div_le_exp_sub_log hd h10) hPα
  have C11 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1) ≤
      WithZero.exp (-(P : ℤ)) := by
    have heq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1 =
        ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 - (d₀ : v.adicCompletion ℚ)) /
          (d₀ : v.adicCompletion ℚ) := by
      field_simp
    rw [heq]
    exact le_trans (valued_div_le_exp_sub_log hd h11) hPα
  refine ⟨C10, C11, ?_⟩

  have hq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) ≠ 0 :=
    ne_zero_of_valued_sub_one_le hP C11
  have hh11 : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := by
    intro h0
    exact hq (by rw [h0, zero_div])
  have hq1 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ)) = 1 :=
    valued_eq_one_of_sub_one_le hP C11

  have R : Valued.v (((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) -
        (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)) /
          ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ))) ≤ WithZero.exp (-(M : ℤ)) :=
    le_trans (valued_div_le_exp_sub_log hc hratio) hMβ

  have heq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
        ((a₀ : v.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) - 1 =
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) -
          (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)) /
            ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)) *
        ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ)) +
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1) := by
    field_simp
    ring
  rw [heq]
  refine Valuation.map_add_le _ ?_ (le_trans C11 (exp_neg_natCast_le_of_le hMP))
  rw [Valuation.map_mul, hq1, mul_one]
  exact R

private theorem ne_zero_and_valued_div_le_of_lower_row (d₀ : (v.adicCompletion ℚ)ˣ) {P : ℕ} (hP : 1 ≤ P) {α : ℤ}
    (hPα : WithZero.exp (α - WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))) ≤ WithZero.exp (-(P : ℤ)))
    {h : GL (Fin 2) (v.adicCompletion ℚ)}
    (h10 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ WithZero.exp α)
    (h11 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 - (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp α) :
    (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 ∧
      Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ WithZero.exp (-(P : ℤ)) := by
  have hd : (d₀ : v.adicCompletion ℚ) ≠ 0 := d₀.ne_zero
  have C10 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 / (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp (-(P : ℤ)) := le_trans (valued_div_le_exp_sub_log hd h10) hPα
  have C11 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1) ≤
      WithZero.exp (-(P : ℤ)) := by
    have heq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) - 1 =
        ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 - (d₀ : v.adicCompletion ℚ)) /
          (d₀ : v.adicCompletion ℚ) := by
      field_simp
    rw [heq]
    exact le_trans (valued_div_le_exp_sub_log hd h11) hPα
  have hq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ) ≠ 0 :=
    ne_zero_of_valued_sub_one_le hP C11
  have hh11 : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := by
    intro h0
    exact hq (by rw [h0, zero_div])
  refine ⟨hh11, ?_⟩
  have heq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 =
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 / (d₀ : v.adicCompletion ℚ)) /
        ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 / (d₀ : v.adicCompletion ℚ)) := by
    field_simp
  rw [heq, map_div₀, valued_eq_one_of_sub_one_le hP C11, div_one]
  exact C10

end Bridge

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section LastColumn

variable {F : Type*} [CommRing F]

private theorem iotaGL_mul_radicalP21 (h : GL (Fin 2) F) (x : Fin 2 → F) :
    iotaGL h * radicalP21 x = radicalP21 ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) * iotaGL h := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem apply_radicalP21_mul {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (x : Fin 2 → F) (g : GL (Fin 3) F) : W (radicalP21 x * g) = ψ (x 1) * W g := by
  have h := hW 0 (x 1) (x 0) g
  rwa [zero_add] at h

private theorem apply_iotaGL_mul_radicalP21 {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (h : GL (Fin 2) F) (x : Fin 2 → F) :
    W (iotaGL h * radicalP21 x) = ψ (((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 1) * W (iotaGL h) := by
  rw [iotaGL_mul_radicalP21, apply_radicalP21_mul hW]

private def rowTwo (h : GL (Fin 2) F) : Fin 2 → F := fun j => (h : Matrix (Fin 2) (Fin 2) F) 1 j

private theorem rowTwo_dotProduct (h : GL (Fin 2) F) (x : Fin 2 → F) :
    rowTwo h ⬝ᵥ x = ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 1 := rfl

private def dotForm (ζ : Fin 2 → F) : (Fin 2 → F) →+ F :=
  AddMonoidHom.mk' (fun x => ζ ⬝ᵥ x) (fun x y => dotProduct_add ζ x y)

private def dotChar (ψ : AddChar F ℂ) (ζ : Fin 2 → F) : AddChar (Fin 2 → F) ℂ :=
  ψ.compAddMonoidHom (dotForm ζ)

@[scoped simp] private theorem dotChar_apply (ψ : AddChar F ℂ) (ζ x : Fin 2 → F) : dotChar ψ ζ x = ψ (ζ ⬝ᵥ x) := rfl

private theorem sum_product_dotChar (ψ : AddChar F ℂ) (ζ : Fin 2 → F) (s₀ s₁ : Finset F) :
    ∑ p ∈ s₀ ×ˢ s₁, dotChar ψ ζ ![p.1, p.2] = (∑ a ∈ s₀, ψ (ζ 0 * a)) * ∑ b ∈ s₁, ψ (ζ 1 * b) := by
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [dotChar_apply, ← AddChar.map_add_eq_mul]
  congr 1
  simp [dotProduct, Fin.sum_univ_two]

omit [CommRing F] in

private theorem vecPair_injective : Function.Injective fun p : F × F => (![p.1, p.2] : Fin 2 → F) :=
  fun p q hpq => Prod.ext (by simpa using congrFun hpq 0) (by simpa using congrFun hpq 1)

end LastColumn
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section RowTwoCut

variable {F : Type*} [CommRing F]

private def rowTwoCut (ψ : AddChar F ℂ) (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (W : GL (Fin 3) F → ℂ) :
    GL (Fin 3) F → ℂ :=
  ∑ x ∈ s, ψ (-(ξ ⬝ᵥ x)) • gl3AmbientRightTranslate (R := ℂ) (radicalP21 x) W

private theorem rowTwoCut_mem_gl3CyclicSubspace (ψ : AddChar F ℂ) (ξ : Fin 2 → F) (s : Finset (Fin 2 → F))
    {W V : GL (Fin 3) F → ℂ} (hV : V ∈ gl3CyclicSubspace W) : rowTwoCut ψ ξ s V ∈ gl3CyclicSubspace W :=
  Submodule.sum_mem _ fun x _ =>
    Submodule.smul_mem _ _ (gl3AmbientRightTranslate_mem_gl3CyclicSubspace W (radicalP21 x) hV)

private theorem rowTwoCut_apply (ψ : AddChar F ℂ) (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (W : GL (Fin 3) F → ℂ)
    (g : GL (Fin 3) F) : rowTwoCut ψ ξ s W g = ∑ x ∈ s, ψ (-(ξ ⬝ᵥ x)) * W (g * radicalP21 x) := by
  simp only [rowTwoCut, Finset.sum_apply, Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul]

private theorem rowTwoCut_apply_iotaGL {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (h : GL (Fin 2) F) :
    rowTwoCut ψ ξ s W (iotaGL h) =
      (∑ x ∈ s, ψ (((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 1 - ξ ⬝ᵥ x)) * W (iotaGL h) := by
  rw [rowTwoCut_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [apply_iotaGL_mul_radicalP21 hW, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_eq_sub]

private theorem rowTwoCut_apply_iotaGL_eq_sum_dotChar {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (h : GL (Fin 2) F) :
    rowTwoCut ψ ξ s W (iotaGL h) = (∑ x ∈ s, dotChar ψ (rowTwo h - ξ) x) * W (iotaGL h) := by
  rw [rowTwoCut_apply_iotaGL hW]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dotChar_apply, sub_dotProduct, rowTwo_dotProduct]

private theorem rowTwoCut_apply_iotaGL_of_forall_eq_one {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (h : GL (Fin 2) F)
    (hs : ∀ x ∈ s, dotChar ψ (rowTwo h - ξ) x = 1) :
    rowTwoCut ψ ξ s W (iotaGL h) = (s.card : ℂ) * W (iotaGL h) := by
  rw [rowTwoCut_apply_iotaGL_eq_sum_dotChar hW, Finset.sum_congr rfl hs, Finset.sum_const, nsmul_eq_mul,
    mul_one]

private theorem rowTwoCut_apply_iotaGL_eq_zero {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (ξ : Fin 2 → F) (s : Finset (Fin 2 → F)) (h : GL (Fin 2) F) (hs : ∑ x ∈ s, dotChar ψ (rowTwo h - ξ) x = 0) :
    rowTwoCut ψ ξ s W (iotaGL h) = 0 := by
  rw [rowTwoCut_apply_iotaGL_eq_sum_dotChar hW, hs, zero_mul]

end RowTwoCut
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section PointwiseTriviality

variable {F : Type*} [CommRing F]

private theorem addChar_eq_one_of_apply_ne_zero {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} {g k : GL (Fin 3) F} (c : F)
    (hinv : W (g * k) = W g) (hc : W (g * k) = ψ c * W g) (hg : W g ≠ 0) : ψ c = 1 := by
  apply mul_right_cancel₀ hg
  rw [one_mul, ← hc, hinv]

private theorem addChar_rowTwo_eq_one {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) {x : Fin 2 → F} (hx : radicalP21 x ∈ S)
    {h : GL (Fin 2) F} (hh : W (iotaGL h) ≠ 0) : ψ (((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) 1) = 1 :=
  addChar_eq_one_of_apply_ne_zero _ (hS _ hx (iotaGL h)) (apply_iotaGL_mul_radicalP21 hW h x) hh

private theorem addChar_ratio_eq_one {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) {t : GL (Fin 2) F} {y c : F}
    (hty : t * unipotentGL2 y = unipotentGL2 c * t) (hy : iotaGL (unipotentGL2 y) ∈ S)
    (ht : W (iotaGL t) ≠ 0) : ψ c = 1 := by
  refine addChar_eq_one_of_apply_ne_zero c (hS _ hy (iotaGL t)) ?_ ht
  rw [← map_mul, hty, map_mul, iotaGL_unipotentGL2, hW c 0 0, add_zero]

end PointwiseTriviality
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section CosetCharacterSum

variable {A : Type*} [AddCommGroup A] (B : AddSubgroup A)

private theorem apply_eq_of_mk_eq (χ : AddChar A ℂ) (hχ : ∀ b ∈ B, χ b = 1) {x y : A} (hxy : (x : A ⧸ B) = y) :
    χ x = χ y := by
  have hB : -x + y ∈ B := QuotientAddGroup.eq.mp hxy
  calc χ x = χ x * χ (-x + y) := by rw [hχ _ hB, mul_one]
    _ = χ (x + (-x + y)) := (AddChar.map_add_eq_mul χ _ _).symm
    _ = χ y := by rw [add_neg_cancel_left]

private theorem apply_out_add (χ : AddChar A ℂ) (hχ : ∀ b ∈ B, χ b = 1) (a : A) (q : A ⧸ B) :
    χ ((a : A ⧸ B) + q).out = χ a * χ q.out := by
  rw [← AddChar.map_add_eq_mul]
  apply apply_eq_of_mk_eq B χ hχ
  rw [QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']

private theorem sum_out_eq_card [Fintype (A ⧸ B)] (χ : AddChar A ℂ) (h : ∀ a, χ a = 1) :
    ∑ q : A ⧸ B, χ q.out = (Fintype.card (A ⧸ B) : ℂ) := by
  simp [h]

private theorem sum_out_eq_zero [Fintype (A ⧸ B)] (χ : AddChar A ℂ) (hχ : ∀ b ∈ B, χ b = 1) {a : A} (ha : χ a ≠ 1) :
    ∑ q : A ⧸ B, χ q.out = 0 := by
  have h₁ : ∑ q : A ⧸ B, χ ((a : A ⧸ B) + q).out = ∑ q : A ⧸ B, χ q.out :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective (a : A ⧸ B)) _ _ fun _ => rfl
  simp_rw [apply_out_add B χ hχ a] at h₁
  rw [← Finset.mul_sum] at h₁
  exact eq_zero_of_mul_eq_self_left ha h₁

private def cosetReps {V : Type*} [DecidableEq V] [Fintype (A ⧸ B)] (f : A → V) : Finset V :=
  (Finset.univ : Finset (A ⧸ B)).image fun q => f q.out

private theorem mem_cosetReps {V : Type*} [DecidableEq V] [Fintype (A ⧸ B)] (f : A → V) {y : V}
    (hy : y ∈ cosetReps B f) : ∃ a : A, y = f a := by
  simp only [cosetReps, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨q, rfl⟩ := hy
  exact ⟨q.out, rfl⟩

private theorem sum_cosetReps {V : Type*} [DecidableEq V] [Fintype (A ⧸ B)] (f : A → V) (hf : Function.Injective f)
    (g : V → ℂ) : ∑ x ∈ cosetReps B f, g x = ∑ q : A ⧸ B, g (f q.out) := by
  have hinj : Function.Injective fun q : A ⧸ B => f q.out := fun _ _ hqq => Quotient.out_injective (hf hqq)
  exact Finset.sum_image hinj.injOn

private theorem card_cosetReps {V : Type*} [DecidableEq V] [Fintype (A ⧸ B)] (f : A → V) (hf : Function.Injective f) :
    (cosetReps B f).card = Fintype.card (A ⧸ B) := by
  have hinj : Function.Injective fun q : A ⧸ B => f q.out := fun _ _ hqq => Quotient.out_injective (hf hqq)
  rw [cosetReps, Finset.card_image_of_injective _ hinj, Finset.card_univ]

private theorem card_cosetReps_ne_zero {V : Type*} [DecidableEq V] [Fintype (A ⧸ B)] (f : A → V)
    (hf : Function.Injective f) : (cosetReps B f).card ≠ 0 := by
  rw [card_cosetReps B f hf]
  exact (Fintype.card_pos_iff.mpr ⟨(0 : A ⧸ B)⟩).ne'

end CosetCharacterSum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section ResidueSystem

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def integerBall (t : v.adicCompletion ℚ) : AddSubgroup (v.adicCompletionIntegers ℚ) where
  carrier := {r | Valued.v (r : v.adicCompletion ℚ) ≤ Valued.v t}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    push_cast
    rwa [Valuation.map_neg]

private theorem mem_integerBall {t : v.adicCompletion ℚ} {r : v.adicCompletionIntegers ℚ} :
    r ∈ integerBall v t ↔ Valued.v (r : v.adicCompletion ℚ) ≤ Valued.v t := Iff.rfl

private theorem isOpen_integerBall {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    IsOpen (integerBall v t : Set (v.adicCompletionIntegers ℚ)) :=
  (NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht).preimage continuous_subtype_val

private theorem finite_quotient_integerBall {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    Finite (v.adicCompletionIntegers ℚ ⧸ integerBall v t) :=
  AddSubgroup.quotient_finite_of_isOpen _ (isOpen_integerBall v ht)

private def scaledChar (ψ : AddChar (v.adicCompletion ℚ) ℂ) (z u : v.adicCompletion ℚ) :
    AddChar (v.adicCompletionIntegers ℚ) ℂ :=
  ψ.compAddMonoidHom
    (AddMonoidHom.mk' (fun r : v.adicCompletionIntegers ℚ => z * (u * (r : v.adicCompletion ℚ)))
      (fun a b => by push_cast; ring))

@[scoped simp] private theorem scaledChar_apply (ψ : AddChar (v.adicCompletion ℚ) ℂ) (z u : v.adicCompletion ℚ)
    (r : v.adicCompletionIntegers ℚ) : scaledChar v ψ z u r = ψ (z * (u * (r : v.adicCompletion ℚ))) := rfl

private theorem exists_residueSystem (ψ : AddChar (v.adicCompletion ℚ) ℂ) {t : v.adicCompletion ℚ} (ht : t ≠ 0)
    {u : v.adicCompletion ℚ} (hu : u ≠ 0) :
    ∃ s : Finset (v.adicCompletion ℚ), s.card ≠ 0 ∧
      (∀ y ∈ s, ∃ r : v.adicCompletionIntegers ℚ, y = u * r) ∧
      ∀ z : v.adicCompletion ℚ,
        (∀ r : v.adicCompletionIntegers ℚ, Valued.v (r : v.adicCompletion ℚ) ≤ Valued.v t →
          ψ (z * (u * r)) = 1) →
        ((∀ r : v.adicCompletionIntegers ℚ, ψ (z * (u * r)) = 1) → ∑ y ∈ s, ψ (z * y) = (s.card : ℂ)) ∧
        ((∃ r : v.adicCompletionIntegers ℚ, ψ (z * (u * r)) ≠ 1) → ∑ y ∈ s, ψ (z * y) = 0) := by
  classical
  haveI : Finite (v.adicCompletionIntegers ℚ ⧸ integerBall v t) := finite_quotient_integerBall v ht
  haveI : Fintype (v.adicCompletionIntegers ℚ ⧸ integerBall v t) := Fintype.ofFinite _
  have hf : Function.Injective fun r : v.adicCompletionIntegers ℚ => u * (r : v.adicCompletion ℚ) :=
    fun a b hab => Subtype.ext (mul_left_cancel₀ hu hab)
  refine ⟨cosetReps (integerBall v t) _, card_cosetReps_ne_zero _ _ hf, ?_, ?_⟩
  · intro y hy
    obtain ⟨r, rfl⟩ := mem_cosetReps (integerBall v t) _ hy
    exact ⟨r, rfl⟩
  · intro z hball
    have hχ : ∀ b ∈ integerBall v t, scaledChar v ψ z u b = 1 := fun b hb =>
      (scaledChar_apply v ψ z u b).trans (hball b ((mem_integerBall v).mp hb))
    rw [sum_cosetReps (integerBall v t) _ hf, card_cosetReps (integerBall v t) _ hf]
    refine ⟨fun hall => ?_, fun ⟨r₀, hr₀⟩ => ?_⟩
    · simpa only [scaledChar_apply] using
        sum_out_eq_card (integerBall v t) (scaledChar v ψ z u)
          fun r => (scaledChar_apply v ψ z u r).trans (hall r)
    · simpa only [scaledChar_apply] using
        sum_out_eq_zero (integerBall v t) (scaledChar v ψ z u) hχ
          (a := r₀) fun h => hr₀ ((scaledChar_apply v ψ z u r₀).symm.trans h)

end ResidueSystem
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section CosetSum

variable {G : Type*} [Group G] (K : Subgroup G)

private theorem apply_eq_of_mk_eq_of_rightInvariant (φ : G → ℂ) (hφ : ∀ k ∈ K, ∀ x, φ (x * k) = φ x) {x y : G}
    (hxy : (x : G ⧸ K) = y) : φ x = φ y := by
  have hK : x⁻¹ * y ∈ K := QuotientGroup.eq.mp hxy
  rw [← hφ _ hK x, mul_inv_cancel_left]

private theorem out_mk_one_mem : ((1 : G) : G ⧸ K).out ∈ K := by
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' ((1 : G) : G ⧸ K)).symm
  rwa [inv_one, one_mul] at h

private theorem sum_apply_mul_out [Fintype (G ⧸ K)] (φ : G → ℂ) (hφ : ∀ k ∈ K, ∀ x, φ (x * k) = φ x) (a : G) :
    ∑ q : G ⧸ K, φ (a * q.out) = ∑ q : G ⧸ K, φ q.out := by
  have h₁ : ∀ q : G ⧸ K, φ (a * q.out) = φ (a • q).out := fun q =>
    apply_eq_of_mk_eq_of_rightInvariant K φ hφ
      ((MulAction.Quotient.mk_smul_out K a q).trans (QuotientGroup.out_eq' (a • q)).symm)
  calc ∑ q : G ⧸ K, φ (a * q.out) = ∑ q : G ⧸ K, φ (a • q).out := Finset.sum_congr rfl fun q _ => h₁ q
    _ = ∑ q : G ⧸ K, φ q.out :=
        Fintype.sum_bijective _ (MulAction.bijective (β := G ⧸ K) a) _ _ fun _ => rfl

private theorem sum_ne_zero_of_forall_eq_zero_or_eq_one {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h01 : ∀ i, f i = 0 ∨ f i = 1) {i₀ : ι} (hi₀ : f i₀ = 1) : ∑ i, f i ≠ 0 := by
  classical
  have hsum : ∑ i, f i = ((Finset.univ.filter fun i => f i ≠ 0).card : ℂ) := by
    rw [← Finset.sum_filter_ne_zero]
    rw [Finset.sum_congr rfl fun i hi => (h01 i).resolve_left (Finset.mem_filter.mp hi).2, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [hsum]
  exact_mod_cast Finset.card_ne_zero_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, by rw [hi₀]; exact one_ne_zero⟩)

end CosetSum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section PrescribedCell

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isGL3PsiWhittakerFn_of_mem_span {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W V : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (hV : V ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ V := by
  refine (mem_gl3PsiWhittakerFnSpace_iff ψ V).mp (Submodule.span_le.mpr ?_ hV)
  rintro _ ⟨g, rfl⟩
  exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ g ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)

private theorem exists_bump_of_isCompact {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (t₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1)
    (hsmall : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      U ≤ U₁ ∧ ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 := by
  obtain ⟨U, hUo, hUle, W', hW'mem, hinv, hsupp, ht₀⟩ := hsmall
  have hW'law : IsGL3PsiWhittakerFn ψ W' := isGL3PsiWhittakerFn_of_mem_span v hW hW'mem

  haveI : CompactSpace U₁ := isCompact_iff_compactSpace.mp hU₁
  have hKo : IsOpen ((U.subgroupOf U₁ : Subgroup U₁) : Set U₁) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  haveI : Finite (U₁ ⧸ U.subgroupOf U₁) := Subgroup.quotient_finite_of_isOpen _ hKo
  haveI : Fintype (U₁ ⧸ U.subgroupOf U₁) := Fintype.ofFinite _

  set F : LocalGL3 v → ℂ :=
    ∑ q : U₁ ⧸ U.subgroupOf U₁, gl3AmbientRightTranslate (R := ℂ) (iotaGL (q.out : GL (Fin 2) (v.adicCompletion ℚ))) W'
    with hF
  have hFmem : F ∈ gl3CyclicSubspace W :=
    Submodule.sum_mem _ fun q _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hW'mem
  have hFiota : ∀ h : GL (Fin 2) (v.adicCompletion ℚ),
      F (iotaGL h) = ∑ q : U₁ ⧸ U.subgroupOf U₁, W' (iotaGL (h * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) := by
    intro h
    simp only [hF, Finset.sum_apply, gl3AmbientRightTranslate_apply, map_mul]

  have hφ : ∀ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ k ∈ U.subgroupOf U₁, ∀ x : U₁,
      W' (iotaGL (h * ((x * k : U₁) : GL (Fin 2) (v.adicCompletion ℚ)))) =
        W' (iotaGL (h * (x : GL (Fin 2) (v.adicCompletion ℚ)))) := by
    intro h k hk x
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact hinv _ (Subgroup.mem_subgroupOf.mp hk) _

  have h01 : ∀ q : U₁ ⧸ U.subgroupOf U₁,
      W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 0 ∨
        W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 1 := by
    intro q
    by_cases hz : W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 0
    · exact Or.inl hz
    right
    obtain ⟨x, u, hu, hxu⟩ := hsupp _ hz
    have hn : unipotentGL2 x = t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ * t₀⁻¹ :=
      eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq hxu.symm)
    have hψx : ψ x = 1 := by
      apply hψU₁
      rw [hn]
      have hgrp : t₀⁻¹ * (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ * t₀⁻¹) * t₀ =
          (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ := by group
      rw [hgrp]
      exact U₁.mul_mem q.out.2 (U₁.inv_mem (hUle hu))
    rw [hxu, hinv u hu, map_mul, iotaGL_unipotentGL2, hW'law x 0 0, add_zero, ht₀, hψx, mul_one]
  have hone : W' (iotaGL (t₀ * ((((1 : U₁) : U₁ ⧸ U.subgroupOf U₁).out : U₁) : GL (Fin 2) (v.adicCompletion ℚ)))) =
      1 := by
    rw [hinv _ (Subgroup.mem_subgroupOf.mp (out_mk_one_mem (U.subgroupOf U₁))), ht₀]
  have hc : F (iotaGL t₀) ≠ 0 := by
    rw [hFiota]
    exact sum_ne_zero_of_forall_eq_zero_or_eq_one _ h01 hone
  refine ⟨(F (iotaGL t₀))⁻¹ • F, Submodule.smul_mem _ _ hFmem, ?_, ?_, ?_⟩
  ·
    intro k hk h
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [hFiota, hFiota]
    have := sum_apply_mul_out (U.subgroupOf U₁)
      (fun x : U₁ => W' (iotaGL (h * (x : GL (Fin 2) (v.adicCompletion ℚ))))) (hφ h) ⟨k, hk⟩
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  ·
    intro h hne
    simp only [Pi.smul_apply, smul_eq_mul] at hne
    have hne' := right_ne_zero_of_mul hne
    rw [hFiota] at hne'
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    obtain ⟨x, u, hu, hxu⟩ := hsupp _ hq
    refine ⟨x, u * (q.out : GL (Fin 2) (v.adicCompletion ℚ))⁻¹, U₁.mul_mem (hUle hu) (U₁.inv_mem q.out.2), ?_⟩
    rw [eq_mul_inv_of_mul_eq hxu, mul_assoc]
  ·
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hc

end PrescribedCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section ResidueSystemValued

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_integer_eq_of_valued_le {u y : v.adicCompletion ℚ} (hu : u ≠ 0) (hy : Valued.v y ≤ Valued.v u) :
    ∃ r : v.adicCompletionIntegers ℚ, y = u * r := by
  have hmem : u⁻¹ * y ∈ v.adicCompletionIntegers ℚ := by
    show Valued.v (u⁻¹ * y) ≤ 1
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hu)), mul_one]
    exact hy
  exact ⟨⟨u⁻¹ * y, hmem⟩, (mul_inv_cancel_left₀ hu y).symm⟩

private theorem valued_mul_integer_le (u : v.adicCompletion ℚ) (r : v.adicCompletionIntegers ℚ) :
    Valued.v (u * (r : v.adicCompletion ℚ)) ≤ Valued.v u := by
  rw [map_mul]
  exact mul_le_of_le_one_right' r.2

private theorem exists_residueSystem_valued (ψ : AddChar (v.adicCompletion ℚ) ℂ) {u t : v.adicCompletion ℚ}
    (hu : u ≠ 0)
    (ht : t ≠ 0) :
    ∃ s : Finset (v.adicCompletion ℚ), s.card ≠ 0 ∧ (∀ y ∈ s, Valued.v y ≤ Valued.v u) ∧
      ∀ z : v.adicCompletion ℚ,
        (∀ y : v.adicCompletion ℚ, Valued.v y ≤ Valued.v u * Valued.v t → ψ (z * y) = 1) →
        ((∀ y : v.adicCompletion ℚ, Valued.v y ≤ Valued.v u → ψ (z * y) = 1) →
          ∑ y ∈ s, ψ (z * y) = (s.card : ℂ)) ∧
        ((∃ y : v.adicCompletion ℚ, Valued.v y ≤ Valued.v u ∧ ψ (z * y) ≠ 1) → ∑ y ∈ s, ψ (z * y) = 0) := by
  obtain ⟨s, hcard, hs, hsum⟩ := exists_residueSystem v ψ ht hu
  refine ⟨s, hcard, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨r, rfl⟩ := hs y hy
    exact valued_mul_integer_le v u r
  · have hball : ∀ r : v.adicCompletionIntegers ℚ, Valued.v (r : v.adicCompletion ℚ) ≤ Valued.v t →
        ψ (z * (u * r)) = 1 := fun r hr =>
      hz _ (by rw [map_mul]; exact mul_le_mul_right hr _)
    obtain ⟨h₁, h₂⟩ := hsum z hball
    refine ⟨fun hall => h₁ fun r => hall _ (valued_mul_integer_le v u r), fun ⟨y, hy, hne⟩ => ?_⟩
    obtain ⟨r, rfl⟩ := exists_integer_eq_of_valued_le v hu hy
    exact h₂ ⟨r, hne⟩

end ResidueSystemValued
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Elements

private theorem upperUnipotent3_mem_congruenceGL {m : ℕ} {x y z : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-(m : ℤ))) (hy : Valued.v y ≤ WithZero.exp (-(m : ℤ)))
    (hz : Valued.v z ≤ WithZero.exp (-(m : ℤ))) :
    upperUnipotent3 x y z ∈ congruenceGL v (Fin 3) m := by
  have he : WithZero.exp (-(m : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hxy : Valued.v (x * y - z) ≤ WithZero.exp (-(m : ℤ)) := by
    refine Valuation.map_sub_le _ ?_ hz
    rw [Valuation.map_mul]
    calc Valued.v x * Valued.v y ≤ WithZero.exp (-(m : ℤ)) * 1 := mul_le_mul' hx (hy.trans he)
      _ = WithZero.exp (-(m : ℤ)) := mul_one _
  have hnx : Valued.v (-x) ≤ WithZero.exp (-(m : ℤ)) := by rwa [Valuation.map_neg]
  have hny : Valued.v (-y) ≤ WithZero.exp (-(m : ℤ)) := by rwa [Valuation.map_neg]
  have hinv : (((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  refine (mem_congruenceGL_iff v).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
        | (simp; done) | simpa using hx | simpa using hy | simpa using hz
  · rw [hinv]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp; done) | simpa using hnx | simpa using hny | simpa using hxy

private theorem radicalP21_mem_congruenceGL {m : ℕ} {w : Fin 2 → v.adicCompletion ℚ}
    (h0 : Valued.v (w 0) ≤ WithZero.exp (-(m : ℤ))) (h1 : Valued.v (w 1) ≤ WithZero.exp (-(m : ℤ))) :
    radicalP21 w ∈ congruenceGL v (Fin 3) m := by
  show upperUnipotent3 0 (w 1) (w 0) ∈ congruenceGL v (Fin 3) m
  exact upperUnipotent3_mem_congruenceGL v (by simp) h1 h0

end Elements
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section Law

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ}

private theorem eq_one_of_mul_eq_self {c a : ℂ} (h : c * a = a) (ha : a ≠ 0) : c = 1 := by
  have h' : (c - 1) * a = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact sub_eq_zero.mp h''
  · exact absurd h'' ha

private theorem exists_forall_addChar_eq_one {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) :
    ∃ m : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(m : ℤ)) → ψ x = 1 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  obtain ⟨Uv, hUo, hUv⟩ := hsm
  obtain ⟨m, hm⟩ := exists_congruenceGL_le_comap_conj v Uv hUo g
  refine ⟨m, fun x hx => ?_⟩
  have hk : upperUnipotent3 x 0 0 ∈ congruenceGL v (Fin 3) m :=
    upperUnipotent3_mem_congruenceGL v hx (by simp) (by simp)
  have h1 : W (upperUnipotent3 x 0 0 * g) = W g := by
    have h := hUv _ (hm _ hk) g
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h
  have h2 := hW x 0 0 g
  rw [h1, add_zero] at h2
  exact eq_one_of_mul_eq_self h2.symm hg

variable {W₀ : LocalGL3 v → ℂ}

private theorem addChar_ratio_mul_eq_one (hW : IsGL3PsiWhittakerFn ψ W₀) {k' : ℕ}
    (hK : ∀ k ∈ congruenceGL v (Fin 3) k', ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g) (a d : (v.adicCompletion ℚ)ˣ)
    (ht : W₀ (iotaGL (diagUnits2 a d)) ≠ 0) {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-(k' : ℤ))) :
    ψ ((a : v.adicCompletion ℚ) * ((d⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) = 1 := by
  have hk : upperUnipotent3 y 0 0 ∈ congruenceGL v (Fin 3) k' :=
    upperUnipotent3_mem_congruenceGL v hy (by simp) (by simp)
  have h1 : W₀ (iotaGL (diagUnits2 a d) * upperUnipotent3 y 0 0) = W₀ (iotaGL (diagUnits2 a d)) := hK _ hk _
  have h2 : iotaGL (diagUnits2 a d) * upperUnipotent3 y 0 0 =
      upperUnipotent3 ((a : v.adicCompletion ℚ) * ((d⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) 0 0 *
        (iotaGL (diagUnits2 a d) : LocalGL3 v) := by
    rw [← iotaGL_unipotentGL2, ← iotaGL_unipotentGL2, ← map_mul, ← map_mul, diagUnits2_mul_unipotentGL2]
  rw [h2, hW _ 0 0 _, add_zero] at h1
  exact eq_one_of_mul_eq_self h1 ht

private theorem addChar_d_mul_eq_one (hW : IsGL3PsiWhittakerFn ψ W₀) {k' : ℕ}
    (hK : ∀ k ∈ congruenceGL v (Fin 3) k', ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g) (a d : (v.adicCompletion ℚ)ˣ)
    (ht : W₀ (iotaGL (diagUnits2 a d)) ≠ 0) {z : v.adicCompletion ℚ} (hz : Valued.v z ≤ WithZero.exp (-(k' : ℤ))) :
    ψ ((d : v.adicCompletion ℚ) * z) = 1 := by
  have hk : radicalP21 ![0, z] ∈ congruenceGL v (Fin 3) k' :=
    radicalP21_mem_congruenceGL v (by simp) (by simpa using hz)
  have h1 : W₀ (iotaGL (diagUnits2 a d) * radicalP21 ![0, z]) = W₀ (iotaGL (diagUnits2 a d)) := hK _ hk _
  have h3 : (((diagUnits2 a d : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *ᵥ
      ![0, z]) 1 = (d : v.adicCompletion ℚ) * z := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [apply_iotaGL_mul_radicalP21 hW, h3] at h1
  exact eq_one_of_mul_eq_self h1 ht

end Law
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section Transport

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ}

private theorem addChar_ne_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ) (x : v.adicCompletion ℚ) : ψ x ≠ 0 := by
  intro h0
  have h := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at h
  exact one_ne_zero h

private theorem isOpen_comap_conj {G : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))}
    (hG : IsOpen (G : Set (GL (Fin 2) (v.adicCompletion ℚ)))) (l : GL (Fin 2) (v.adicCompletion ℚ)) :
    IsOpen ((G.comap (MulAut.conj l).toMonoidHom : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hc : Continuous fun k : GL (Fin 2) (v.adicCompletion ℚ) => l * k * l⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h__af := hG.preimage hc
  simp only [Subgroup.coe_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h__af ⊢
  exact h__af

private theorem comap_conj_le {G U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))} {l : GL (Fin 2) (v.adicCompletion ℚ)}
    (h : G ≤ U₀.comap (MulAut.conj l⁻¹).toMonoidHom) : G.comap (MulAut.conj l).toMonoidHom ≤ U₀ := by
  intro k hk
  have hk' : l * k * l⁻¹ ∈ G := by
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
  have h' := h hk'
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ← mul_assoc,
    inv_mul_cancel, one_mul, inv_mul_cancel_right] using h'

private theorem exists_bump_transport {W W' : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ W)
    (hW' : W' ∈ gl3CyclicSubspace W)
    {t : GL (Fin 2) (v.adicCompletion ℚ)} {G : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))}
    (hinv : ∀ k ∈ G, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h))
    (hsupp : ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
      ∃ x : v.adicCompletion ℚ, ∃ k ∈ G, h = unipotentGL2 x * t * k)
    (hval : W' (iotaGL t) = 1) (x₀ : v.adicCompletion ℚ) (l : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∃ W'' ∈ gl3CyclicSubspace W,
      (∀ k ∈ G.comap (MulAut.conj l).toMonoidHom, ∀ h : GL (Fin 2) (v.adicCompletion ℚ),
        W'' (iotaGL (h * k)) = W'' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W'' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ G.comap (MulAut.conj l).toMonoidHom,
          h = unipotentGL2 x * (unipotentGL2 x₀ * t * l) * k) ∧
      W'' (iotaGL (unipotentGL2 x₀ * t * l)) = 1 := by
  have hlaw : IsGL3PsiWhittakerFn ψ W' := isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ hW hW'
  have hψ0 : ψ x₀ ≠ 0 := addChar_ne_zero v ψ x₀
  refine ⟨(ψ x₀)⁻¹ • gl3AmbientRightTranslate (R := ℂ) (iotaGL l⁻¹) W',
    Submodule.smul_mem _ _ (gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hW'), ?_, ?_, ?_⟩
  · intro k hk h
    have hk' : l * k * l⁻¹ ∈ G := by
      simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
    simp only [Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul, ← map_mul]
    rw [show h * k * l⁻¹ = h * l⁻¹ * (l * k * l⁻¹) by group, hinv _ hk' (h * l⁻¹)]
  · intro h hh
    simp only [Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul, ← map_mul] at hh
    obtain ⟨x, k, hk, hx⟩ := hsupp (h * l⁻¹) (right_ne_zero_of_mul hh)
    refine ⟨x - x₀, l⁻¹ * k * l, ?_, ?_⟩
    · simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← mul_assoc, mul_inv_cancel,
        one_mul, mul_inv_cancel_right] using hk
    · have hh' : h = unipotentGL2 x * t * k * l := by rw [← hx, inv_mul_cancel_right]
      have hn : unipotentGL2 x = unipotentGL2 (x - x₀) * unipotentGL2 x₀ := by
        rw [← unipotentGL2_add, sub_add_cancel]
      rw [hh', hn]
      group
  · simp only [Pi.smul_apply, gl3AmbientRightTranslate_apply, smul_eq_mul, ← map_mul, mul_inv_cancel_right]
    rw [map_mul, iotaGL_unipotentGL2, hlaw x₀ 0 0 _, add_zero, hval, mul_one, inv_mul_cancel₀ hψ0]

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Formula

variable {F : Type*} [CommRing F]

private def pairSet [DecidableEq F] (s₀ s₁ : Finset F) : Finset (Fin 2 → F) :=
  (s₀ ×ˢ s₁).image fun p : F × F => ![p.1, p.2]

private theorem sum_pairSet_dotChar [DecidableEq F] (ψ : AddChar F ℂ) (ζ : Fin 2 → F) (s₀ s₁ : Finset F) :
    ∑ x ∈ pairSet s₀ s₁, dotChar ψ ζ x = (∑ a ∈ s₀, ψ (ζ 0 * a)) * ∑ b ∈ s₁, ψ (ζ 1 * b) := by
  rw [pairSet, Finset.sum_image fun p _ q _ hpq => vecPair_injective hpq]
  exact sum_product_dotChar ψ ζ s₀ s₁

private theorem rowTwoCut_pairSet_apply_iotaGL [DecidableEq F] {ψ : AddChar F ℂ} {V : GL (Fin 3) F → ℂ}
    (hV : IsGL3PsiWhittakerFn ψ V) (d₀ : F) (s : Finset F) (h : GL (Fin 2) F) :
    rowTwoCut ψ ![0, d₀] (pairSet s s) V (iotaGL h) =
      (∑ z ∈ s, ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 0 * z)) *
        (∑ z ∈ s, ψ (((h : Matrix (Fin 2) (Fin 2) F) 1 1 - d₀) * z)) * V (iotaGL h) := by
  have h0 : (rowTwo h - ![0, d₀]) 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 0 := by simp [rowTwo]
  have h1 : (rowTwo h - ![0, d₀]) 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 - d₀ := by simp [rowTwo]
  rw [rowTwoCut_apply_iotaGL_eq_sum_dotChar hV, sum_pairSet_dotChar, h0, h1]

private theorem bigCell_apply_one_zero (x : F) (a d : Fˣ) (e : F) :
    ((unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (d : F) * e := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem bigCell_apply_one_one (x : F) (a d : Fˣ) (e : F) :
    ((unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (d : F) := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem addChar_entries_eq_one_of_apply_ne_zero {ψ : AddChar F ℂ} {V : GL (Fin 3) F → ℂ}
    (hV : IsGL3PsiWhittakerFn ψ V) {L : Set F} (h0 : (0 : F) ∈ L)
    (hrad : ∀ p ∈ L, ∀ r ∈ L, ∀ g, V (g * radicalP21 ![p, r]) = V g) {h : GL (Fin 2) F}
    (hne : V (iotaGL h) ≠ 0) {z : F} (hz : z ∈ L) :
    ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 0 * z) = 1 ∧ ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 1 * z) = 1 := by
  constructor
  · have hc := apply_iotaGL_mul_radicalP21 hV h ![z, 0]
    have hmv : ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ ![z, 0]) 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 0 * z := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hmv] at hc
    exact addChar_eq_one_of_apply_ne_zero _ (hrad z hz 0 h0 _) hc hne
  · have hc := apply_iotaGL_mul_radicalP21 hV h ![0, z]
    have hmv : ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, z]) 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 * z := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hmv] at hc
    exact addChar_eq_one_of_apply_ne_zero _ (hrad 0 h0 z hz _) hc hne

private theorem unipotentGL2_mulVec_sub (y p r : F) :
    ((unipotentGL2 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ ![p - y * r, r] = ![p, r] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem ratioCut_apply_mul_radicalP21 (ψ : AddChar F ℂ) (c : F) (s : Finset F) {W : GL (Fin 3) F → ℂ}
    {L : Set F} (hW : ∀ y ∈ s, ∀ p ∈ L, ∀ r ∈ L, ∀ g, W (g * radicalP21 ![p - y * r, r]) = W g) {p r : F}
    (hp : p ∈ L) (hr : r ∈ L) (g : GL (Fin 3) F) :
    ratioCut ψ c s W (g * radicalP21 ![p, r]) = ratioCut ψ c s W g := by
  rw [ratioCut_apply, ratioCut_apply]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hcomm : g * radicalP21 ![p, r] * iotaGL (unipotentGL2 y) =
      g * iotaGL (unipotentGL2 y) * radicalP21 ![p - y * r, r] := by
    rw [mul_assoc g (iotaGL _), iotaGL_mul_radicalP21, unipotentGL2_mulVec_sub, mul_assoc]
  rw [hcomm, hW y hy p hp r hr]

private theorem rowTwoCut_ratioCut_apply_iotaGL [DecidableEq F] {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) (c d₀ : F)
    (sM sN : Finset F) {h : GL (Fin 2) F} (x : F) (a d : Fˣ) (e : F)
    (hh : h = unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e) (he : iotaGL (lowerUnipotentGL2 e) ∈ S)
    (hs : ∀ y ∈ sM, iotaGL (conjugatedLower e y) ∈ S) :
    rowTwoCut ψ ![0, d₀] (pairSet sN sN) (ratioCut ψ c sM W) (iotaGL h) =
      (∑ z ∈ sN, ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 0 * z)) *
        (∑ z ∈ sN, ψ (((h : Matrix (Fin 2) (Fin 2) F) 1 1 - d₀) * z)) *
        ((∑ y ∈ sM, ψ (((a : F) * ((d⁻¹ : Fˣ) : F) - c) * y)) * (ψ x * W (iotaGL (diagUnits2 a d)))) := by
  have hV : IsGL3PsiWhittakerFn ψ (ratioCut ψ c sM W) :=
    isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ hW
      (ratioCut_mem_gl3CyclicSubspace ψ c sM (self_mem_gl3CyclicSubspace W))
  have hpoint : W (iotaGL (unipotentGL2 x * diagUnits2 a d * lowerUnipotentGL2 e)) =
      ψ x * W (iotaGL (diagUnits2 a d)) := by
    rw [map_mul, hS _ he, apply_iotaGL_unipotentGL2_mul hW]
  rw [rowTwoCut_pairSet_apply_iotaGL hV]
  subst hh
  rw [ratioCut_apply_iotaGL hW hS c sM x a d e he hs, hpoint]

private theorem rowTwoCut_ratioCut_apply_iotaGL_diagUnits2 [DecidableEq F] {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {S : Set (GL (Fin 3) F)} (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g)
    (h1 : (1 : GL (Fin 3) F) ∈ S) (sM sN : Finset F) (a₀ d₀ : Fˣ) :
    rowTwoCut ψ ![0, (d₀ : F)] (pairSet sN sN) (ratioCut ψ ((a₀ : F) * ((d₀⁻¹ : Fˣ) : F)) sM W)
        (iotaGL (diagUnits2 a₀ d₀)) =
      (sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W (iotaGL (diagUnits2 a₀ d₀))) := by
  have hh : diagUnits2 a₀ d₀ = unipotentGL2 0 * diagUnits2 a₀ d₀ * lowerUnipotentGL2 0 := by simp
  have he : iotaGL (lowerUnipotentGL2 (0 : F)) ∈ S := by simpa using h1
  have hs : ∀ y ∈ sM, iotaGL (conjugatedLower (0 : F) y) ∈ S := fun y _ => by simpa using h1
  have hS₁ : ∑ z ∈ sN, ψ (((diagUnits2 a₀ d₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 * z) =
      (sN.card : ℂ) := by simp
  have hS₂ : ∑ z ∈ sN, ψ ((((diagUnits2 a₀ d₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 - (d₀ : F)) * z) =
      (sN.card : ℂ) := by simp
  have hS₃ : ∑ y ∈ sM, ψ (((a₀ : F) * ((d₀⁻¹ : Fˣ) : F) - (a₀ : F) * ((d₀⁻¹ : Fˣ) : F)) * y) =
      (sM.card : ℂ) := by simp
  rw [rowTwoCut_ratioCut_apply_iotaGL hW hS _ _ sM sN 0 a₀ d₀ 0 hh he hs, hS₁, hS₂, hS₃,
    AddChar.map_zero_eq_one, one_mul]

private theorem rowTwoCut_ratioCut_apply_iotaGL_diagUnits2_ne_zero [DecidableEq F] {ψ : AddChar F ℂ}
    {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {S : Set (GL (Fin 3) F)}
    (hS : ∀ k ∈ S, ∀ g, W (g * k) = W g) (h1 : (1 : GL (Fin 3) F) ∈ S) {sM sN : Finset F} (hM : sM.card ≠ 0)
    (hN : sN.card ≠ 0) {a₀ d₀ : Fˣ} (hW0 : W (iotaGL (diagUnits2 a₀ d₀)) ≠ 0) :
    rowTwoCut ψ ![0, (d₀ : F)] (pairSet sN sN) (ratioCut ψ ((a₀ : F) * ((d₀⁻¹ : Fˣ) : F)) sM W)
        (iotaGL (diagUnits2 a₀ d₀)) ≠ 0 := by
  rw [rowTwoCut_ratioCut_apply_iotaGL_diagUnits2 hW hS h1 sM sN a₀ d₀]
  exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hN) (Nat.cast_ne_zero.mpr hN))
    (mul_ne_zero (Nat.cast_ne_zero.mpr hM) hW0)

private theorem ne_zero_and_addChar_eq_one_of_rowTwoCut_apply_ne_zero [DecidableEq F] {ψ : AddChar F ℂ}
    {V : GL (Fin 3) F → ℂ} (hV : IsGL3PsiWhittakerFn ψ V) {L B : Set F} (h0 : (0 : F) ∈ L)
    (hrad : ∀ p ∈ L, ∀ r ∈ L, ∀ g, V (g * radicalP21 ![p, r]) = V g) {d₀ : F} (hd₀ : ∀ y ∈ L, ψ (d₀ * y) = 1)
    {sN : Finset F}
    (hsum : ∀ z : F, (∀ y ∈ L, ψ (z * y) = 1) → (∃ y ∈ B, ψ (z * y) ≠ 1) → ∑ w ∈ sN, ψ (z * w) = 0)
    {h : GL (Fin 2) F} (hne : rowTwoCut ψ ![0, d₀] (pairSet sN sN) V (iotaGL h) ≠ 0) :
    V (iotaGL h) ≠ 0 ∧ (∀ y ∈ B, ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 0 * y) = 1) ∧
      ∀ y ∈ B, ψ (((h : Matrix (Fin 2) (Fin 2) F) 1 1 - d₀) * y) = 1 := by
  rw [rowTwoCut_pairSet_apply_iotaGL hV] at hne
  have hV0 : V (iotaGL h) ≠ 0 := fun hz => hne (by rw [hz, mul_zero])
  have hL₁ : ∀ y ∈ L, ψ ((h : Matrix (Fin 2) (Fin 2) F) 1 0 * y) = 1 := fun y hy =>
    (addChar_entries_eq_one_of_apply_ne_zero hV h0 hrad hV0 hy).1
  have hL₂ : ∀ y ∈ L, ψ (((h : Matrix (Fin 2) (Fin 2) F) 1 1 - d₀) * y) = 1 := fun y hy => by
    rw [sub_mul, AddChar.map_sub_eq_div, (addChar_entries_eq_one_of_apply_ne_zero hV h0 hrad hV0 hy).2,
      hd₀ y hy, div_one]
  refine ⟨hV0, fun y hy => ?_, fun y hy => ?_⟩
  · by_contra hy1
    exact hne (by rw [hsum _ hL₁ ⟨y, hy, hy1⟩, zero_mul, zero_mul])
  · by_contra hy1
    exact hne (by rw [hsum _ hL₂ ⟨y, hy, hy1⟩, mul_zero, zero_mul])

end Formula
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Level

private theorem exists_level {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : ψ ≠ 1)
    (hball : ∃ m : ℕ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(m : ℤ)) → ψ x = 1) :
    ∃ ℓ : ℤ, (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ℓ) → ψ x = 1) ∧
      ∃ x₁ : v.adicCompletion ℚ, Valued.v x₁ ≤ WithZero.exp (-(ℓ - 1)) ∧ ψ x₁ ≠ 1 := by
  classical
  obtain ⟨x₁, hx₁⟩ := AddChar.ne_one_iff.mp hψ
  have hx₁0 : x₁ ≠ 0 := by
    rintro rfl
    exact hx₁ (AddChar.map_zero_eq_one ψ)
  have hv₁ : Valued.v x₁ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₁0

  have hbdd : ∃ b : ℤ, ∀ ℓ : ℤ, (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ℓ) → ψ x = 1) → b ≤ ℓ := by
    refine ⟨-WithZero.log (Valued.v x₁), fun ℓ hℓ => ?_⟩
    by_contra hlt
    have hlt' : ℓ < -WithZero.log (Valued.v x₁) := lt_of_not_ge hlt
    refine hx₁ (hℓ x₁ ?_)
    rw [← WithZero.exp_log hv₁]
    exact WithZero.exp_le_exp.mpr (by omega)
  obtain ⟨m, hm⟩ := hball
  obtain ⟨ℓ, hℓ, hmin⟩ := Int.exists_least_of_bdd hbdd ⟨(m : ℤ), hm⟩
  refine ⟨ℓ, hℓ, ?_⟩
  by_contra hno
  have hℓ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(ℓ - 1)) → ψ x = 1 := fun x hx => by
    by_contra h
    exact hno ⟨x, hx, h⟩
  have := hmin (ℓ - 1) hℓ'
  omega

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section Reduction

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}

private def TorusBump (W : LocalGL3 v → ℂ) (a d : (v.adicCompletion ℚ)ˣ)
    (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
    Prop :=
  ∃ G : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (G : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ G ≤ U₀ ∧
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ G, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ G, h = unipotentGL2 x * diagUnits2 a d * k) ∧
      W' (iotaGL (diagUnits2 a d)) = 1

private theorem exists_bump_of_factor (hW : IsGL3PsiWhittakerFn ψ W) {t₀ l : GL (Fin 2) (v.adicCompletion ℚ)}
    {x₀ : v.adicCompletion ℚ} {a d : (v.adicCompletion ℚ)ˣ} (hfac : t₀ = unipotentGL2 x₀ * diagUnits2 a d * l)
    (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (htorus : TorusBump v W a d (U₀.comap (MulAut.conj l⁻¹).toMonoidHom)) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ U ≤ U₀ ∧
      ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1 := by
  obtain ⟨G, hGo, hGle, W', hW', hinv, hsupp, hval⟩ := htorus
  obtain ⟨W'', hW'', hinv', hsupp', hval'⟩ := exists_bump_transport v hW hW' hinv hsupp hval x₀ l
  refine ⟨G.comap (MulAut.conj l).toMonoidHom, isOpen_comap_conj v hGo l, comap_conj_le v hGle, W'', hW'', hinv',
    ?_, ?_⟩
  · rw [hfac]
    exact hsupp'
  · rw [hfac]
    exact hval'

private theorem exists_bump_of_torus (hW : IsGL3PsiWhittakerFn ψ W)
    (htorus : ∀ (a d : (v.adicCompletion ℚ)ˣ) (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))),
      IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ))) → TorusBump v W a d U₀)
    (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₀ : IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ U ≤ U₀ ∧
      ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1 := by
  by_cases h11 : (t₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 0
  · exact exists_bump_of_factor v hW (eq_unipotent_mul_diag_mul_antidiag t₀ h11) U₀
      (htorus _ _ _ (isOpen_comap_conj v hU₀ _))
  · exact exists_bump_of_factor v hW (eq_unipotent_mul_diag_mul_lower t₀ h11) U₀
      (htorus _ _ _ (isOpen_comap_conj v hU₀ _))

private theorem exists_cell_bump_of_bump (hW : IsGL3PsiWhittakerFn ψ W)
    (hbump : ∀ (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))),
      IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ))) →
      ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
        IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ U ≤ U₀ ∧
        ∃ W' ∈ gl3CyclicSubspace W,
          (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
          (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
            ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
          W' (iotaGL t₀) = 1)
    (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hU₁' : IsOpen (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 :=
  exists_bump_of_isCompact v hW t₀ U₁ hU₁ hψU₁ (hbump t₀ U₁ hU₁')

end Reduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Algebra

variable {F : Type*} [CommRing F]

private theorem sum_eq_card_of_forall_eq_one {α : Type*} {s : Finset α} {f : α → ℂ} (h : ∀ z ∈ s, f z = 1) :
    ∑ z ∈ s, f z = (s.card : ℂ) := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem unipotent_mul_diag_mul_apply_zero_one (x : F) (a d : Fˣ) (κ : GL (Fin 2) F) :
    ((unipotentGL2 x * diagUnits2 a d * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (a : F) * (κ : Matrix (Fin 2) (Fin 2) F) 0 1 + x * ((d : F) * (κ : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem ratio_sub_eq (a₀ d₀ u w : Fˣ) :
    ((a₀ * u : Fˣ) : F) * (((d₀ * w)⁻¹ : Fˣ) : F) - (a₀ : F) * ((d₀⁻¹ : Fˣ) : F) =
      (a₀ : F) * ((d₀⁻¹ : Fˣ) : F) * ((u : F) * ((w⁻¹ : Fˣ) : F) - 1) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  ring

private theorem unipotent_mul_diag_mul_eq_of_eq (x : F) (a₀ d₀ : Fˣ) {κ : GL (Fin 2) F} {x₁ e₁ : F} {u w : Fˣ}
    (hκ : κ = unipotentGL2 x₁ * diagUnits2 u w * lowerUnipotentGL2 e₁) :
    unipotentGL2 x * diagUnits2 a₀ d₀ * κ =
      unipotentGL2 (x + (a₀ : F) * ((d₀⁻¹ : Fˣ) : F) * x₁) * diagUnits2 (a₀ * u) (d₀ * w) *
        lowerUnipotentGL2 e₁ := by
  rw [hκ]
  calc unipotentGL2 x * diagUnits2 a₀ d₀ * (unipotentGL2 x₁ * diagUnits2 u w * lowerUnipotentGL2 e₁)
      = unipotentGL2 x * (diagUnits2 a₀ d₀ * unipotentGL2 x₁) * diagUnits2 u w * lowerUnipotentGL2 e₁ := by
        simp only [mul_assoc]
    _ = unipotentGL2 x * (unipotentGL2 ((a₀ : F) * ((d₀⁻¹ : Fˣ) : F) * x₁) * diagUnits2 a₀ d₀) * diagUnits2 u w *
          lowerUnipotentGL2 e₁ := by
        rw [diagUnits2_mul_unipotentGL2]
    _ = unipotentGL2 (x + (a₀ : F) * ((d₀⁻¹ : Fˣ) : F) * x₁) * diagUnits2 (a₀ * u) (d₀ * w) *
          lowerUnipotentGL2 e₁ := by
        rw [unipotentGL2_add, ← diagUnits2_mul_diagUnits2]
        simp only [mul_assoc]

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section CellValue

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem rowTwoCut_ratioCut_apply_iotaGL_of_mixedPattern [DecidableEq (v.adicCompletion ℚ)]
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W₀ : GL (Fin 3) (v.adicCompletion ℚ) → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W₀) {k' : ℕ} (hk : 1 ≤ k') {S : Set (GL (Fin 3) (v.adicCompletion ℚ))}
    (hS : ∀ k ∈ S, ∀ g, W₀ (g * k) = W₀ g)
    (hSk : ∀ g : GL (Fin 3) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k' : ℤ))) ∧
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(k' : ℤ))) → g ∈ S)
    {ℓ : ℤ} (hℓ : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (-ℓ) → ψ y = 1)
    (a₀ d₀ : (v.adicCompletion ℚ)ˣ) {Mo Mp P : ℕ} (hMo : 1 ≤ Mo) (hMok : k' ≤ Mo) (hMP : Mo ≤ P)
    (hPk : k' + 2 * Mp ≤ P) {M N : ℤ} (hMp : M ≤ Mp) {sM sN : Finset (v.adicCompletion ℚ)}
    (hsM : ∀ y ∈ sM, Valued.v y ≤ WithZero.exp M) (hsN : ∀ z ∈ sN, Valued.v z ≤ WithZero.exp N)
    (hNd : WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ)) + N - P ≤ -ℓ)
    (hMc : WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ))) + M - Mo ≤ -ℓ)
    (hPc : WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ))) - P ≤ -ℓ)
    (x : v.adicCompletion ℚ) {κ : GL (Fin 2) (v.adicCompletion ℚ)}
    (hκ : MixedPattern v Mo P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
        (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀)
        (iotaGL (unipotentGL2 x * diagUnits2 a₀ d₀ * κ)) =
      ψ x * ((sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W₀ (iotaGL (diagUnits2 a₀ d₀)))) := by
  have hκ' := hκ
  obtain ⟨-, hκ01, hκ10, hκ11⟩ := hκ'
  have hP1 : 1 ≤ P := hMo.trans hMP
  have hκ11ne : (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := ne_zero_of_valued_sub_one_le hP1 hκ11
  have hκ11val : Valued.v ((κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) = 1 :=
    valued_eq_one_of_sub_one_le hP1 hκ11

  obtain ⟨x₁, u, w, e₁, hfac, hx1, hu1, hw1, he1⟩ :
      ∃ (x₁ : v.adicCompletion ℚ) (u w : (v.adicCompletion ℚ)ˣ) (e₁ : v.adicCompletion ℚ),
        κ = unipotentGL2 x₁ * diagUnits2 u w * lowerUnipotentGL2 e₁ ∧
        x₁ = (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 /
          (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ∧
        (u : v.adicCompletion ℚ) = (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ∧
        (w : v.adicCompletion ℚ) = (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ∧
        e₁ = (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
          (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 :=
    ⟨_, _, _, _, eq_unipotent_mul_diag_mul_lower κ hκ11ne, rfl, Units.val_mk0 _, Units.val_mk0 _, rfl⟩
  have hh := unipotent_mul_diag_mul_eq_of_eq x a₀ d₀ hfac

  have hvd : Valued.v (d₀ : v.adicCompletion ℚ) ≤
      WithZero.exp (WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr d₀.ne_zero)).ge
  have hvc : Valued.v ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
      WithZero.exp (WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))) := by
    rw [Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr (div_ne_zero a₀.ne_zero d₀.ne_zero))).ge

  have hve : Valued.v e₁ ≤ WithZero.exp (-((k' : ℤ) + 2 * (Mp : ℤ))) := by
    rw [he1, map_div₀, hκ11val, div_one]
    exact hκ10.trans (WithZero.exp_le_exp.mpr (by omega))
  have he : iotaGL (lowerUnipotentGL2 e₁) ∈ S := hSk _ (iotaGL_lowerUnipotentGL2_entries_le hve)
  have hs : ∀ y ∈ sM, iotaGL (conjugatedLower e₁ y) ∈ S := fun y hy =>
    hSk _ (iotaGL_conjugatedLower_entries_le hve ((hsM y hy).trans (WithZero.exp_le_exp.mpr hMp)))

  have hS₁ : ∀ z ∈ sN,
      ψ ((d₀ : v.adicCompletion ℚ) * (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * z) = 1 :=
    fun z hz => hℓ _ ((valued_mul_le_exp_add (valued_mul_le_exp_add hvd hκ10) (hsN z hz)).trans
      (WithZero.exp_le_exp.mpr (by omega)))
  have hS₂ : ∀ z ∈ sN,
      ψ (((d₀ : v.adicCompletion ℚ) * (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 -
        (d₀ : v.adicCompletion ℚ)) * z) = 1 := fun z hz => by
    rw [← mul_sub_one]
    exact hℓ _ ((valued_mul_le_exp_add (valued_mul_le_exp_add hvd hκ11) (hsN z hz)).trans
      (WithZero.exp_le_exp.mpr (by omega)))
  have huw : (u : v.adicCompletion ℚ) * ((w⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
        ((κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
          (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) := by
    rw [Units.val_inv_eq_inv_val, hu1, hw1, ← div_eq_mul_inv, div_div]
  have hdet := valued_det_div_sq_sub_one_le_of_mixedPattern hMP hP1 hκ
  have hS₃ : ∀ y ∈ sM,
      ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
        ((κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          ((κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
            (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) - 1) * y) = 1 :=
    fun y hy => hℓ _ ((valued_mul_le_exp_add (valued_mul_le_exp_add hvc hdet) (hsM y hy)).trans
      (WithZero.exp_le_exp.mpr (by omega)))

  have hvx1 : Valued.v x₁ ≤ WithZero.exp (-(P : ℤ)) := by
    rw [hx1, map_div₀, hκ11val, div_one]
    exact hκ01
  have hψ1 : ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₁) = 1 :=
    hℓ _ ((valued_mul_le_exp_add hvc hvx1).trans (WithZero.exp_le_exp.mpr (by omega)))
  have hphase : ψ (x + (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₁) =
      ψ x := by
    rw [AddChar.map_add_eq_mul, hψ1, mul_one]

  have hu' : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k' : ℤ)) := by
    rw [hu1]
    exact (valued_det_div_sub_one_le_of_mixedPattern hMP hP1 hκ).trans (exp_neg_natCast_le_of_le hMok)
  have hw' : Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k' : ℤ)) := by
    rw [hw1]
    exact hκ11.trans (exp_neg_natCast_le_of_le (hMok.trans hMP))
  have hWfac : W₀ (iotaGL (diagUnits2 (a₀ * u) (d₀ * w))) = W₀ (iotaGL (diagUnits2 a₀ d₀)) := by
    rw [← diagUnits2_mul_diagUnits2, map_mul]
    exact hS _ (hSk _ (iotaGL_diagUnits2_entries_le hk hu' hw')) _

  rw [rowTwoCut_ratioCut_apply_iotaGL hW hS _ _ sM sN _ _ _ _ hh he hs, unipotent_mul_diag_mul_apply_one_zero,
    unipotent_mul_diag_mul_apply_one_one, ratio_sub_eq, huw, hphase, hWfac, sum_eq_card_of_forall_eq_one hS₁,
    sum_eq_card_of_forall_eq_one hS₂, sum_eq_card_of_forall_eq_one hS₃]
  ring

end CellValue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace upperUnipotent3 radicalP21 embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnits2 coe_diagUnits2"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section TorusFurniture

private theorem exists_valued_eq_exp (n : ℤ) : ∃ u : v.adicCompletion ℚ, u ≠ 0 ∧ Valued.v u = WithZero.exp n := by
  obtain ⟨t, ht0, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) v n.natAbs
  by_cases hn : n ≤ 0
  · refine ⟨t, ht0, ?_⟩
    rw [hvt, Int.ofNat_natAbs_of_nonpos hn, neg_neg]
  · refine ⟨t⁻¹, inv_ne_zero ht0, ?_⟩
    rw [map_inv₀, hvt, ← WithZero.exp_neg, Int.natAbs_of_nonneg (not_le.mp hn).le, neg_neg]

variable {v}

private theorem sum_addChar_eq_card {ψ : AddChar (v.adicCompletion ℚ) ℂ} {s : Finset (v.adicCompletion ℚ)}
    {z : v.adicCompletion ℚ} (h : ∀ y ∈ s, ψ (z * y) = 1) : ∑ y ∈ s, ψ (z * y) = (s.card : ℂ) := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem units_mul_inv_eq_div (a₀ d₀ : (v.adicCompletion ℚ)ˣ) :
    (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ) := by
  rw [Units.val_inv_eq_inv_val, div_eq_mul_inv]

private theorem valued_units_eq_exp_log (d₀ : (v.adicCompletion ℚ)ˣ) : Valued.v (d₀ : v.adicCompletion ℚ) =
    WithZero.exp (WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))) :=
  (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr d₀.ne_zero)).symm

private theorem valued_units_mul_inv_eq_exp_log (a₀ d₀ : (v.adicCompletion ℚ)ˣ) :
    Valued.v ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
    WithZero.exp (WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))) := by
  rw [units_mul_inv_eq_div]
  exact (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr (div_ne_zero a₀.ne_zero d₀.ne_zero))).symm

private theorem addChar_mul_eq_one_of_valued_le {ψ : AddChar (v.adicCompletion ℚ) ℂ} {ℓ : ℤ}
    (hℓ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ℓ) → ψ x = 1) {c y : v.adicCompletion ℚ} {a b : ℤ}
    (hc : Valued.v c ≤ WithZero.exp a) (hy : Valued.v y ≤ WithZero.exp b) (hab : a + b ≤ -ℓ) : ψ (c * y) = 1 :=
  hℓ _ ((valued_mul_le_exp_add hc hy).trans (WithZero.exp_le_exp.mpr hab))

private theorem iotaGL_conjugatedLower_mem_congruenceGL {k M : ℕ} {e y : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) (hy : Valued.v y ≤ WithZero.exp (M : ℤ)) :
    iotaGL (conjugatedLower e y) ∈ congruenceGL v (Fin 3) k :=
  (mem_congruenceGL_iff v).mpr (iotaGL_conjugatedLower_entries_le he hy)

private theorem iotaGL_lowerUnipotentGL2_mem_congruenceGL {k M : ℕ} {e : v.adicCompletion ℚ}
    (he : Valued.v e ≤ WithZero.exp (-((k : ℤ) + 2 * (M : ℤ)))) :
    iotaGL (lowerUnipotentGL2 e) ∈ congruenceGL v (Fin 3) k :=
  (mem_congruenceGL_iff v).mpr (iotaGL_lowerUnipotentGL2_entries_le (M := M) he)

end TorusFurniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section TorusCut

variable {v}
variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W₀ : LocalGL3 v → ℂ} {k' : ℕ} {ℓ : ℤ} {x₁ : v.adicCompletion ℚ}
  {a₀ d₀ : (v.adicCompletion ℚ)ˣ} {Mo Mp P : ℕ} {M N : ℤ} {sM sN : Finset (v.adicCompletion ℚ)}

private structure TorusData (ψ : AddChar (v.adicCompletion ℚ) ℂ) (W₀ : LocalGL3 v → ℂ) (k' : ℕ) (ℓ : ℤ)
    (x₁ : v.adicCompletion ℚ) (a₀ d₀ : (v.adicCompletion ℚ)ˣ) (Mo Mp P : ℕ) (M N : ℤ)
    (sM sN : Finset (v.adicCompletion ℚ)) : Prop where
  law : IsGL3PsiWhittakerFn ψ W₀
  hk : 1 ≤ k'
  smooth : ∀ k ∈ congruenceGL v (Fin 3) k', ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g
  level : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ℓ) → ψ x = 1
  hx₁ : Valued.v x₁ ≤ WithZero.exp (-(ℓ - 1))
  hψx₁ : ψ x₁ ≠ 1
  ratio_triv : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (-(k' : ℤ)) →
    ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) = 1
  d_triv : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ WithZero.exp (-(k' : ℤ)) → ψ ((d₀ : v.adicCompletion ℚ) * z) = 1
  hMo : 1 ≤ Mo
  hMok : k' ≤ Mo
  hMP : Mo ≤ P
  hPk : k' + 2 * Mp ≤ P
  hM : M = (Mo : ℤ) - ℓ - WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))
  hMp : M ≤ (Mp : ℤ)
  hN : N = (P : ℤ) - ℓ - WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))
  sM_le : ∀ y ∈ sM, Valued.v y ≤ WithZero.exp M
  sM_ne : sM.card ≠ 0
  sM_sum : ∀ z : v.adicCompletion ℚ,
    (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (-(k' : ℤ)) → ψ (z * y) = 1) →
    (∃ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp M ∧ ψ (z * y) ≠ 1) → ∑ y ∈ sM, ψ (z * y) = 0
  sN_le : ∀ y ∈ sN, Valued.v y ≤ WithZero.exp N
  sN_ne : sN.card ≠ 0
  sN_sum : ∀ z : v.adicCompletion ℚ,
    (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ))) → ψ (z * y) = 1) →
    (∃ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp N ∧ ψ (z * y) ≠ 1) → ∑ y ∈ sN, ψ (z * y) = 0

namespace TorusData

variable (D : TorusData ψ W₀ k' ℓ x₁ a₀ d₀ Mo Mp P M N sM sN)
include D

private theorem one_le_P : 1 ≤ P := le_trans D.hMo D.hMP

private theorem log_c₀_le :
    WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ))) ≤ (k' : ℤ) - ℓ := by
  have h := valued_le_of_forall_addChar_mul_eq_one D.hx₁ D.hψx₁ (N := -(k' : ℤ))
    (c := (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) D.ratio_triv
  rw [valued_units_mul_inv_eq_exp_log a₀ d₀, WithZero.exp_le_exp] at h
  omega

private theorem log_d₀_le : WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ)) ≤ (k' : ℤ) - ℓ := by
  have h := valued_le_of_forall_addChar_mul_eq_one D.hx₁ D.hψx₁ (N := -(k' : ℤ)) (c := (d₀ : v.adicCompletion ℚ))
    D.d_triv
  rw [valued_units_eq_exp_log d₀, WithZero.exp_le_exp] at h
  omega

private theorem ratioCut_law : IsGL3PsiWhittakerFn ψ
    (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀) :=
  isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ D.law
    (ratioCut_mem_gl3CyclicSubspace ψ _ sM (self_mem_gl3CyclicSubspace W₀))

private theorem smooth_set : ∀ k ∈ ((congruenceGL v (Fin 3) k' : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)),
    ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g := fun k hk g => D.smooth k hk g

private theorem ratioCut_rad : ∀ p ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ)))},
    ∀ r ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ)))}, ∀ g : LocalGL3 v,
      ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀
        (g * radicalP21 ![p, r]) =
      ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀ g := by
  intro p hp r hr g
  refine ratioCut_apply_mul_radicalP21 ψ _ sM (L := {y | Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ)))})
    (fun y hy p' hp' r' hr' g' => D.smooth _ (radicalP21_mem_congruenceGL v ?_ ?_) g') hp hr g
  · have hyr : Valued.v (y * r') ≤ WithZero.exp (-(k' : ℤ)) :=
      (valued_mul_le_exp_add ((D.sM_le y hy).trans (WithZero.exp_le_exp.mpr D.hMp)) hr').trans
        (WithZero.exp_le_exp.mpr (by omega))
    have hp'' : Valued.v p' ≤ WithZero.exp (-(k' : ℤ)) := le_trans hp' (WithZero.exp_le_exp.mpr (by omega))
    simpa using Valuation.map_sub_le _ hp'' hyr
  · have hr'' : Valued.v r' ≤ WithZero.exp (-(k' : ℤ)) := le_trans hr' (WithZero.exp_le_exp.mpr (by omega))
    simpa using hr''

private theorem d₀_rad : ∀ y ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ)))},
    ψ ((d₀ : v.adicCompletion ℚ) * y) = 1 := fun y hy =>
  D.d_triv y (le_trans hy (WithZero.exp_le_exp.mpr (by omega)))

private theorem sN_sum' : ∀ z : v.adicCompletion ℚ,
    (∀ y ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-((k' : ℤ) + (Mp : ℤ)))}, ψ (z * y) = 1) →
    (∃ y ∈ {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp N}, ψ (z * y) ≠ 1) → ∑ w ∈ sN, ψ (z * w) = 0 :=
  fun z hz ⟨y, hy, hne⟩ => D.sN_sum z (fun y hy => hz y hy) ⟨y, hy, hne⟩

private theorem hPα :
    WithZero.exp (-(ℓ + N) - WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ))) ≤ WithZero.exp (-(P : ℤ)) :=
  WithZero.exp_le_exp.mpr (by rw [D.hN]; omega)

private theorem hMβ :
    WithZero.exp (-(ℓ + M) - WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))) ≤
      WithZero.exp (-(Mo : ℤ)) :=
  WithZero.exp_le_exp.mpr (by rw [D.hM]; omega)

private theorem inCell_of_ne_zero [DecidableEq (v.adicCompletion ℚ)] {h : GL (Fin 2) (v.adicCompletion ℚ)}
    (hne : rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
      (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀)
      (iotaGL h) ≠ 0) :
    InCell v a₀ d₀ Mo P h := by
  obtain ⟨hV0, h10, h11⟩ := ne_zero_and_addChar_eq_one_of_rowTwoCut_apply_ne_zero D.ratioCut_law (by simp)
    D.ratioCut_rad D.d₀_rad D.sN_sum' hne

  have H10 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ WithZero.exp (-(ℓ + N)) :=
    valued_le_of_forall_addChar_mul_eq_one D.hx₁ D.hψx₁ fun z hz => h10 z hz
  have H11 : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 - (d₀ : v.adicCompletion ℚ)) ≤
      WithZero.exp (-(ℓ + N)) :=
    valued_le_of_forall_addChar_mul_eq_one D.hx₁ D.hψx₁ fun z hz => h11 z hz

  obtain ⟨h11ne, he'⟩ := ne_zero_and_valued_div_le_of_lower_row d₀ D.one_le_P D.hPα H10 H11
  have he : Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ WithZero.exp (-((k' : ℤ) + 2 * (Mp : ℤ))) :=
    he'.trans (WithZero.exp_le_exp.mpr (by have := D.hPk; omega))
  have hle : iotaGL (lowerUnipotentGL2 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)) ∈
        ((congruenceGL v (Fin 3) k' : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) :=
    iotaGL_lowerUnipotentGL2_mem_congruenceGL (M := Mp) he
  have hls : ∀ y ∈ sM, iotaGL (conjugatedLower ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) y) ∈
        ((congruenceGL v (Fin 3) k' : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := fun y hy =>
    iotaGL_conjugatedLower_mem_congruenceGL he ((D.sM_le y hy).trans (WithZero.exp_le_exp.mpr D.hMp))

  have hfac := eq_unipotent_mul_diag_mul_lower h h11ne
  have hratio := ratioCut_apply_iotaGL D.law D.smooth_set
    ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM
    ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 / (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
    (Units.mk0
      ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det / (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
      (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) h11ne))
    (Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) h11ne) _ hle hls
  rw [← hfac] at hratio
  rw [hratio] at hV0
  have hsum_ne := left_ne_zero_of_mul hV0
  have hW_ne := right_ne_zero_of_mul hV0

  have hpoint : W₀ (iotaGL h) = ψ ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 /
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) * W₀ (iotaGL (diagUnits2
        (Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
          (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) h11ne))
        (Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) h11ne))) := by
    conv_lhs => rw [hfac]
    rw [map_mul, D.smooth _ hle, apply_iotaGL_unipotentGL2_mul D.law]
  rw [hpoint] at hW_ne
  have hWd := right_ne_zero_of_mul hW_ne

  have hz : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (-(k' : ℤ)) →
      ψ ((((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
          (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) h11ne) : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) *
          (((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) h11ne)⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) -
          (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) * y) = 1 := by
    intro y hy
    rw [sub_mul, AddChar.map_sub_eq_div, addChar_ratio_mul_eq_one v D.law D.smooth _ _ hWd hy, D.ratio_triv y hy,
      div_one]
  have hall : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp M →
      ψ ((((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
          (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) h11ne) : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) *
          (((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) h11ne)⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) -
          (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) * y) = 1 := by
    intro y hy
    by_contra hy1
    exact hsum_ne (D.sM_sum _ hz ⟨y, hy, hy1⟩)
  have Hβ := valued_le_of_forall_addChar_mul_eq_one D.hx₁ D.hψx₁ hall

  have hratio_eq : (((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
        (div_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero h) h11ne) : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ) *
        (((Units.mk0 ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) h11ne)⁻¹ : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ) -
        (a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det /
          ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) -
        (a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ) := by
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    ring
  rw [hratio_eq] at Hβ
  exact inCell_of_valued_entries a₀ d₀ D.hMo D.hMP D.hPα D.hMβ H10 H11 Hβ

private theorem inCell_iff_exists_mem {h : GL (Fin 2) (v.adicCompletion ℚ)} :
    InCell v a₀ d₀ Mo P h ↔ ∃ x : v.adicCompletion ℚ, ∃ κ ∈ mixedCongruence v Mo P D.hMP,
      h = unipotentGL2 x * diagUnits2 a₀ d₀ * κ := by
  rw [inCell_iff a₀ d₀ D.hMo D.hMP]
  constructor
  · rintro ⟨x, κ, hκ, rfl⟩
    exact ⟨x, κ, (mem_mixedCongruence_iff v).mpr hκ, rfl⟩
  · rintro ⟨x, κ, hκ, rfl⟩
    exact ⟨x, κ, (mem_mixedCongruence_iff v).mp hκ, rfl⟩

private theorem torusBump [DecidableEq (v.adicCompletion ℚ)]
    (hcell : ∀ (x : v.adicCompletion ℚ) (κ : GL (Fin 2) (v.adicCompletion ℚ)),
      MixedPattern v Mo P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) →
      rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
        (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀)
        (iotaGL (unipotentGL2 x * diagUnits2 a₀ d₀ * κ)) =
      ψ x * ((sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W₀ (iotaGL (diagUnits2 a₀ d₀)))))
    (hW0 : W₀ (iotaGL (diagUnits2 a₀ d₀)) ≠ 0) :
    ∃ W' ∈ gl3CyclicSubspace W₀,
      (∀ k ∈ mixedCongruence v Mo P D.hMP, ∀ h : GL (Fin 2) (v.adicCompletion ℚ),
        W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ mixedCongruence v Mo P D.hMP, h = unipotentGL2 x * diagUnits2 a₀ d₀ * k) ∧
      W' (iotaGL (diagUnits2 a₀ d₀)) = 1 := by

  set C : ℂ := (sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W₀ (iotaGL (diagUnits2 a₀ d₀))) with hC_def
  have hC : C ≠ 0 := mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr D.sN_ne) (Nat.cast_ne_zero.mpr D.sN_ne))
    (mul_ne_zero (Nat.cast_ne_zero.mpr D.sM_ne) hW0)
  set F₂ : LocalGL3 v → ℂ := rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
    (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀) with hF₂_def

  have hsupp : ∀ h : GL (Fin 2) (v.adicCompletion ℚ), F₂ (iotaGL h) ≠ 0 →
      ∃ x : v.adicCompletion ℚ, ∃ k ∈ mixedCongruence v Mo P D.hMP, h = unipotentGL2 x * diagUnits2 a₀ d₀ * k :=
    fun h hh => D.inCell_iff_exists_mem.mp (D.inCell_of_ne_zero hh)

  have hval : ∀ (x : v.adicCompletion ℚ), ∀ κ ∈ mixedCongruence v Mo P D.hMP,
      F₂ (iotaGL (unipotentGL2 x * diagUnits2 a₀ d₀ * κ)) = ψ x * C := fun x κ hκ =>
    hcell x κ ((mem_mixedCongruence_iff v).mp hκ).1
  refine ⟨C⁻¹ • F₂, Submodule.smul_mem _ _
    (rowTwoCut_mem_gl3CyclicSubspace ψ _ _ (ratioCut_mem_gl3CyclicSubspace ψ _ sM (self_mem_gl3CyclicSubspace W₀))),
    ?_, ?_, ?_⟩
  ·
    intro k hk h
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    by_cases hcellh : ∃ x : v.adicCompletion ℚ, ∃ κ ∈ mixedCongruence v Mo P D.hMP,
        h = unipotentGL2 x * diagUnits2 a₀ d₀ * κ
    · obtain ⟨x, κ, hκ, rfl⟩ := hcellh
      rw [mul_assoc (unipotentGL2 x * diagUnits2 a₀ d₀) κ k, hval x _ (Subgroup.mul_mem _ hκ hk), hval x κ hκ]
    · have h0 : F₂ (iotaGL h) = 0 := by
        by_contra hne
        exact hcellh (hsupp h hne)
      have h0' : F₂ (iotaGL (h * k)) = 0 := by
        by_contra hne
        obtain ⟨x, κ, hκ, hx⟩ := hsupp (h * k) hne
        refine hcellh ⟨x, κ * k⁻¹, Subgroup.mul_mem _ hκ (Subgroup.inv_mem _ hk), ?_⟩
        rw [← mul_assoc, ← hx, mul_inv_cancel_right]
      rw [h0, h0']
  ·
    intro h hh
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact hsupp h (right_ne_zero_of_mul hh)
  ·
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := hval 0 1 (Subgroup.one_mem _)
    rw [unipotentGL2_zero, one_mul, mul_one, AddChar.map_zero_eq_one, one_mul] at h1
    rw [h1, inv_mul_cancel₀ hC]

end TorusData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end TorusCut
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

section Final

variable {v}

private def CellValueFact (ψ : AddChar (v.adicCompletion ℚ) ℂ) (a₀ d₀ : (v.adicCompletion ℚ)ˣ) : Prop :=
  ∀ ⦃W₀ : LocalGL3 v → ℂ⦄ ⦃k' : ℕ⦄ ⦃ℓ : ℤ⦄ ⦃x₁ : v.adicCompletion ℚ⦄ ⦃Mo Mp P : ℕ⦄ ⦃M N : ℤ⦄
    ⦃sM sN : Finset (v.adicCompletion ℚ)⦄, TorusData ψ W₀ k' ℓ x₁ a₀ d₀ Mo Mp P M N sM sN →
    ∀ [DecidableEq (v.adicCompletion ℚ)] (x : v.adicCompletion ℚ) (κ : GL (Fin 2) (v.adicCompletion ℚ)),
      MixedPattern v Mo P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) →
      rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
        (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀)
        (iotaGL (unipotentGL2 x * diagUnits2 a₀ d₀ * κ)) =
      ψ x * ((sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W₀ (iotaGL (diagUnits2 a₀ d₀))))

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}

private theorem torusBump_of_datum (hψ : ψ ≠ 1) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (a₀ d₀ : (v.adicCompletion ℚ)ˣ) (hcell : CellValueFact ψ a₀ d₀)
    (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (hU₀ : IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    TorusBump v W a₀ d₀ U₀ := by
  classical
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.mp hne
  obtain ⟨Uv, hUo, hUv⟩ := hsm

  set g₁' : LocalGL3 v := (iotaGL (diagUnits2 a₀ d₀))⁻¹ * g₁ with hg₁'
  set W₀ : LocalGL3 v → ℂ := gl3AmbientRightTranslate (R := ℂ) g₁' W with hW₀_def
  have hW₀mem : W₀ ∈ gl3CyclicSubspace W := translate_mem_gl3CyclicSubspace W g₁'
  have hW₀law : IsGL3PsiWhittakerFn ψ W₀ := isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ hW hW₀mem
  have hW₀t : W₀ (iotaGL (diagUnits2 a₀ d₀)) ≠ 0 := by
    rw [hW₀_def, gl3AmbientRightTranslate_apply, hg₁', ← mul_assoc, mul_inv_cancel, one_mul]
    exact hg₁

  obtain ⟨k₀, hk₀⟩ := exists_congruenceGL_translate_invariant v W hUo hUv g₁'
  have hsmooth : ∀ k ∈ congruenceGL v (Fin 3) (max k₀ 1), ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g := by
    intro k hk g
    rw [hW₀_def, gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply]
    exact hk₀ k (congruenceGL_antitone v (le_max_left k₀ 1) hk) g

  obtain ⟨m, hm⟩ := exists_forall_addChar_eq_one v hW ⟨Uv, hUo, hUv⟩ hne
  obtain ⟨ℓ, hℓ, x₁, hx₁, hψx₁⟩ := exists_level v hψ ⟨m, hm⟩

  obtain ⟨m₀, hm₀⟩ := exists_forall_mixedCongruence_le v U₀ hU₀
  set k' : ℕ := max k₀ 1 with hk'_def
  set Mo : ℕ := max (max m₀ 1) k' with hMo_def
  set M : ℤ := (Mo : ℤ) - ℓ - WithZero.log (Valued.v ((a₀ : v.adicCompletion ℚ) / (d₀ : v.adicCompletion ℚ)))
    with hM_def
  set Mp : ℕ := M.toNat with hMp_def
  set P : ℕ := max Mo (k' + 2 * Mp) with hP_def
  set N : ℤ := (P : ℤ) - ℓ - WithZero.log (Valued.v (d₀ : v.adicCompletion ℚ)) with hN_def

  obtain ⟨uM, huM0, huM⟩ := exists_valued_eq_exp v M
  obtain ⟨tM, htM0, htM⟩ := exists_valued_eq_exp v (-(k' : ℤ) - M)
  obtain ⟨sM, hsMne, hsMle, hsMsum⟩ := exists_residueSystem_valued v ψ huM0 htM0
  obtain ⟨uN, huN0, huN⟩ := exists_valued_eq_exp v N
  obtain ⟨tN, htN0, htN⟩ := exists_valued_eq_exp v (-((k' : ℤ) + (Mp : ℤ)) - N)
  obtain ⟨sN, hsNne, hsNle, hsNsum⟩ := exists_residueSystem_valued v ψ huN0 htN0
  have hballM : Valued.v uM * Valued.v tM = WithZero.exp (-(k' : ℤ)) := by
    rw [huM, htM, ← WithZero.exp_add]
    congr 1
    ring
  have hballN : Valued.v uN * Valued.v tN = WithZero.exp (-((k' : ℤ) + (Mp : ℤ))) := by
    rw [huN, htN, ← WithZero.exp_add]
    congr 1
    ring

  have D : TorusData ψ W₀ k' ℓ x₁ a₀ d₀ Mo Mp P M N sM sN :=
    { law := hW₀law
      hk := le_max_right k₀ 1
      smooth := hsmooth
      level := hℓ
      hx₁ := hx₁
      hψx₁ := hψx₁
      ratio_triv := fun y hy => addChar_ratio_mul_eq_one v hW₀law hsmooth a₀ d₀ hW₀t hy
      d_triv := fun z hz => addChar_d_mul_eq_one v hW₀law hsmooth a₀ d₀ hW₀t hz
      hMo := le_trans (le_max_right m₀ 1) (le_max_left _ _)
      hMok := le_max_right _ _
      hMP := le_max_left _ _
      hPk := le_max_right _ _
      hM := rfl
      hMp := Int.self_le_toNat M
      hN := rfl
      sM_le := fun y hy => by rw [← huM]; exact hsMle y hy
      sM_ne := hsMne
      sM_sum := fun z hz hex => (hsMsum z fun y hy => hz y (by rwa [hballM] at hy)).2
        (by obtain ⟨y, hy, hy1⟩ := hex; exact ⟨y, by rw [huM]; exact hy, hy1⟩)
      sN_le := fun y hy => by rw [← huN]; exact hsNle y hy
      sN_ne := hsNne
      sN_sum := fun z hz hex => (hsNsum z fun y hy => hz y (by rwa [hballN] at hy)).2
        (by obtain ⟨y, hy, hy1⟩ := hex; exact ⟨y, by rw [huN]; exact hy, hy1⟩) }

  obtain ⟨W', hW'mem, hinv, hsupp, hval⟩ := D.torusBump (hcell D) hW₀t
  exact ⟨mixedCongruence v Mo P D.hMP, isOpen_mixedCongruence v _,
    hm₀ Mo P _ (le_trans (le_max_left m₀ 1) (le_max_left _ _)), W', gl3CyclicSubspace_le_of_mem hW₀mem hW'mem,
    hinv, hsupp, hval⟩

private theorem TorusData.cellValue [DecidableEq (v.adicCompletion ℚ)] {W₀ : LocalGL3 v → ℂ} {k' : ℕ} {ℓ : ℤ}
    {x₁ : v.adicCompletion ℚ} {a₀ d₀ : (v.adicCompletion ℚ)ˣ} {Mo Mp P : ℕ} {M N : ℤ}
    {sM sN : Finset (v.adicCompletion ℚ)}
    (D : TorusData ψ W₀ k' ℓ x₁ a₀ d₀ Mo Mp P M N sM sN)
    (x : v.adicCompletion ℚ) {κ : GL (Fin 2) (v.adicCompletion ℚ)}
    (hκ : MixedPattern v Mo P (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    rowTwoCut ψ ![0, (d₀ : v.adicCompletion ℚ)] (pairSet sN sN)
        (ratioCut ψ ((a₀ : v.adicCompletion ℚ) * ((d₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) sM W₀)
        (iotaGL (unipotentGL2 x * diagUnits2 a₀ d₀ * κ)) =
      ψ x * ((sN.card : ℂ) * (sN.card : ℂ) * ((sM.card : ℂ) * W₀ (iotaGL (diagUnits2 a₀ d₀)))) :=
  rowTwoCut_ratioCut_apply_iotaGL_of_mixedPattern D.law D.hk
    (S := ((congruenceGL v (Fin 3) k' : Subgroup (LocalGL3 v)) : Set (LocalGL3 v))) D.smooth_set
    (fun g hg => (mem_congruenceGL_iff v).mpr hg) D.level a₀ d₀ D.hMo D.hMok D.hMP D.hPk D.hMp D.sM_le D.sN_le
    (by rw [D.hN]; omega) (by rw [D.hM]; omega)
    (by have h₁ := D.log_c₀_le; have h₂ := D.hMok; have h₃ := D.hMP; omega) x hκ

private theorem cellValueFact {a₀ d₀ : (v.adicCompletion ℚ)ˣ} : CellValueFact ψ a₀ d₀ := by
  intro W₀ k' ℓ x₁ Mo Mp P M N sM sN D inst x κ hκ
  exact D.cellValue x hκ

private theorem exists_iotaGL_bump (hψ : ψ ≠ 1) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₀ : IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ U ≤ U₀ ∧
      ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1 :=
  exists_bump_of_torus v hW (fun a d U hU => torusBump_of_datum hψ hW hsm hne a d cellValueFact U hU) t₀ U₀ hU₀

private theorem exists_iotaGL_cell_bump (hψ : ψ ≠ 1) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hU₁' : IsOpen (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 :=
  exists_cell_bump_of_bump v hW (exists_iotaGL_bump hψ hW hsm hne) t₀ U₁ hU₁ hU₁' hψU₁

end Final
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end LanglandsTunnell.CubicInduction.Kirillov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction.Kirillov"

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₀ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₀ : IsOpen (U₀ : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧ U ≤ U₀ ∧
      ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1 :=
  LanglandsTunnell.CubicInduction.Kirillov.exists_iotaGL_bump hψ hW hsm hne t₀ U₀ hU₀

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump (solution)
