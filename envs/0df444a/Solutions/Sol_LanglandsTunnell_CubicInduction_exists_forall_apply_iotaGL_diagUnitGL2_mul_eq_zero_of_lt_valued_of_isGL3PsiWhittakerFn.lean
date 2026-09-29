-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8d4f1807-692c-5d53-94a8-0523170775ed

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

open LanglandsTunnell.CubicInduction

section QuarryInfra
open NumberField.TateGlobal

namespace LocalZetaRational

variable (v : HeightOneSpectrum (𝓞 ℚ))

def EntriesLE (A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (e : WithZero (Multiplicative ℤ)) : Prop :=
  ∀ i j, Valued.v (A i j) ≤ e

theorem entriesLE_mul {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {x y : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A x) (hB : EntriesLE v B y) : EntriesLE v (A * B) (x * y) := by
  intro i j
  have hterm : ∀ l, Valued.v (A i l * B l j) ≤ x * y := fun l => by
    rw [Valuation.map_mul]
    exact mul_le_mul' (hA i l) (hB l j)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem entriesLE_add {A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) (hB : EntriesLE v B e) : EntriesLE v (A + B) e := fun i j => by
  rw [Matrix.add_apply]
  exact le_trans (Valuation.map_add _ _ _) (max_le (hA i j) (hB i j))

theorem entriesLE_neg {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e : WithZero (Multiplicative ℤ)}
    (hA : EntriesLE v A e) : EntriesLE v (-A) e := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]
  exact hA i j

theorem entriesLE_mono {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e e' : WithZero (Multiplicative ℤ)}
    (h : e ≤ e') (hA : EntriesLE v A e) : EntriesLE v A e' := fun i j => (hA i j).trans h

theorem entriesLE_one_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    EntriesLE v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 ∧
      EntriesLE v ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 :=
  (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk

def principalCongruence3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    EntriesLE v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) (WithZero.exp (-(m : ℤ)))}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    intro i j
    rw [Units.val_one, sub_self, Matrix.zero_apply, Valuation.map_zero]
    exact zero_le'
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) +
        ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [hid]
    refine entriesLE_add v ?_ ha'
    simpa only [one_mul] using entriesLE_mul v (entriesLE_one_of_mem v ha).1 hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          (-((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1)) := by
      rw [neg_sub, mul_sub, mul_one, Units.inv_mul]
    rw [hid]
    simpa only [one_mul] using entriesLE_mul v (entriesLE_one_of_mem v ha).2 (entriesLE_neg v ha')

theorem mem_principalCongruence3_iff {m : ℕ} {k : LocalGL3 v} :
    k ∈ principalCongruence3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      EntriesLE v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) (WithZero.exp (-(m : ℤ))) :=
  Iff.rfl

theorem principalCongruence3_le_localMaximalCompact3 (m : ℕ) :
    principalCongruence3 v m ≤ localMaximalCompact3 (𝓞 ℚ) ℚ v := fun _ hk => hk.1

theorem principalCongruence3_antitone {m m' : ℕ} (h : m ≤ m') :
    principalCongruence3 v m' ≤ principalCongruence3 v m := fun _ hk =>
  ⟨hk.1, entriesLE_mono v (WithZero.exp_le_exp.mpr (by omega)) hk.2⟩

theorem conj_mem_principalCongruence3 {m : ℕ} {k g : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hg : g ∈ principalCongruence3 v m) : k * g * k⁻¹ ∈ principalCongruence3 v m := by
  refine ⟨mul_mem (mul_mem hk hg.1) (inv_mem hk), ?_⟩
  have hid : ((k * g * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
        ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [hid]
  have h1 := entriesLE_mul v (entriesLE_one_of_mem v hk).1 hg.2
  have h2 := entriesLE_mul v h1 (entriesLE_one_of_mem v hk).2
  simpa only [one_mul, mul_one] using h2

theorem isOpen_setOf_forall_entry_mem {S : Set (v.adicCompletion ℚ)} (hS : IsOpen S) :
    IsOpen {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} := by
  have h : {A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, A i j ∈ S} =
      ⋂ i, ⋂ j, (fun A : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => A i j) ⁻¹' S := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_id.matrix_elem i j)

theorem exists_setOf_forall_entry_sub_le_subset_of_isOpen
    {A : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))} (hA : IsOpen A)
    {C : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (hC : C ∈ A) :
    ∃ j : ℕ, {X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
      ∀ i l, Valued.v (X i l - C i l) ≤ WithZero.exp (-(j : ℤ))} ⊆ A := by
  obtain ⟨u, hu, huA⟩ := (isOpen_pi_iff'.mp hA) C hC
  have hrow : ∀ i, ∃ w : Fin 3 → Set (v.adicCompletion ℚ),
      (∀ l, IsOpen (w l) ∧ C i l ∈ w l) ∧ Set.univ.pi w ⊆ u i :=
    fun i => (isOpen_pi_iff'.mp (hu i).1) (C i) (hu i).2
  choose w hw hwu using hrow
  have hball : ∀ i l, ∃ j : ℤ,
      {x : v.adicCompletion ℚ | Valued.v (x - C i l) ≤ WithZero.exp (-j)} ⊆ w i l :=
    fun i l => exists_setOf_valued_sub_le_subset_of_isOpen v (hw i l).1 (hw i l).2
  choose jj hjj using hball
  refine ⟨Finset.univ.sup fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat, fun X hX => ?_⟩
  refine huA (Set.mem_univ_pi.mpr fun i => hwu i (Set.mem_univ_pi.mpr fun l => hjj i l ?_))
  have h1 : jj i l ≤ ((jj i l).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (jj i l).toNat ≤ Finset.univ.sup fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat :=
    Finset.le_sup (f := fun p : Fin 3 × Fin 3 => (jj p.1 p.2).toNat) (Finset.mem_univ (i, l))
  exact (hX i l).trans (WithZero.exp_le_exp.mpr (by omega))

theorem isOpen_principalCongruence3 (m : ℕ) : IsOpen (principalCongruence3 v m : Set (LocalGL3 v)) := by
  have hball1 : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
    simpa only [sub_zero, neg_zero, WithZero.exp_zero] using (isClopen_setOf_valued_sub_le v 0 0).isOpen
  have hballm : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))} := by
    simpa only [sub_zero] using (isClopen_setOf_valued_sub_le v 0 (m : ℤ)).isOpen
  have h1 : IsOpen ((fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ 1}}) :=
    (isOpen_setOf_forall_entry_mem v hball1).preimage Units.continuous_val
  have h2 : IsOpen ((fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ 1}}) :=
    (isOpen_setOf_forall_entry_mem v hball1).preimage Units.continuous_coe_inv
  have h3 : IsOpen ((fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) ⁻¹'
      {A | ∀ i j, A i j ∈ {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))}}) :=
    (isOpen_setOf_forall_entry_mem v hballm).preimage (Units.continuous_val.sub continuous_const)
  convert (h1.inter h2).inter h3 using 1
  rfl

theorem exists_principalCongruence3_le_of_isOpen (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v))) :
    ∃ m : ℕ, principalCongruence3 v m ≤ U := by
  have hmem : (U : Set (LocalGL3 v)) ∈ nhds (1 : LocalGL3 v) := hU.mem_nhds (one_mem U)
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hmem
  obtain ⟨T, hT, hTU⟩ := hmem
  rw [Units.embedProduct_apply, inv_one, Units.val_one, mem_nhds_prod_iff] at hT
  obtain ⟨A, hA, B, hB, hABT⟩ := hT
  obtain ⟨A₀, hA₀A, hA₀, h1A₀⟩ := mem_nhds_iff.mp hA
  have hB' : (MulOpposite.op : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) → _) ⁻¹' B ∈
      nhds (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨B₀, hB₀B, hB₀, h1B₀⟩ := mem_nhds_iff.mp hB'
  obtain ⟨j₁, hj₁⟩ := exists_setOf_forall_entry_sub_le_subset_of_isOpen v hA₀ h1A₀
  obtain ⟨j₂, hj₂⟩ := exists_setOf_forall_entry_sub_le_subset_of_isOpen v hB₀ h1B₀
  refine ⟨max j₁ j₂, fun k hk => ?_⟩
  have hball : ∀ {g : LocalGL3 v}, g ∈ principalCongruence3 v (max j₁ j₂) → ∀ j : ℕ, j ≤ max j₁ j₂ →
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) ∈
        {X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i l,
          Valued.v (X i l - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l) ≤ WithZero.exp (-(j : ℤ))} := by
    intro g hg j hj i l
    have h := hg.2 i l
    rw [Matrix.sub_apply] at h
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))
  apply hTU
  show Units.embedProduct _ k ∈ T
  rw [Units.embedProduct_apply]
  exact hABT ⟨hA₀A (hj₁ (hball hk j₁ (le_max_left _ _))),
    hB₀B (hj₂ (hball (inv_mem hk) j₂ (le_max_right _ _)))⟩

theorem exists_level_of_smooth {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ u ∈ Uv, ∀ g, W (g * u) = W g) :
    ∃ m : ℕ, ∀ u ∈ principalCongruence3 v m, ∀ g, W (g * u) = W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  obtain ⟨m, hm⟩ := exists_principalCongruence3_le_of_isOpen v Uv hUo
  exact ⟨m, fun u hu g => hUW u (hm hu) g⟩

theorem coe_iotaGL_diagUnitGL2 (u : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 u) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(u : v.adicCompletion ℚ), 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnitGL2]

end LocalZetaRational

end QuarryInfra

namespace Ws31
namespace TS
theorem torus_mul_upperUnipotent3 (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    (iotaGL (diagUnitGL2 u) : LocalGL3 v) * upperUnipotent3 x y z =
      upperUnipotent3 ((u : v.adicCompletion ℚ) * x) y ((u : v.adicCompletion ℚ) * z) * iotaGL (diagUnitGL2 u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, upperUnipotent3, diagUnitGL2, Matrix.mul_apply, Fin.sum_univ_three]
end Ws31.TS

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (g : LocalGL3 v) :
    ∃ K : ℤ, ∀ a : (v.adicCompletion ℚ)ˣ, WithZero.exp K < Valued.v (a : v.adicCompletion ℚ) →
      W (iotaGL (diagUnitGL2 a) * g) = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, ψv x₀ ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hψv (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have hx₀0 : x₀ ≠ 0 := by rintro rfl; exact hx₀ (AddChar.map_zero_eq_one ψv)
  obtain ⟨Uv, hUo, hUW⟩ := hsm
  let U' : Subgroup (LocalGL3 v) := Uv.map (MulAut.conj g).toMonoidHom
  have hU'o : IsOpen (U' : Set (LocalGL3 v)) := by
    have : (U' : Set (LocalGL3 v)) = (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹) '' (Uv : Set (LocalGL3 v)) := by
      ext k'; simp [U', MulAut.conj_apply]
    rw [this]; exact (Homeomorph.isOpenMap _) _ hUo
  obtain ⟨m, hm⟩ := LocalZetaRational.exists_principalCongruence3_le_of_isOpen v U' hU'o

  set k₀ : ℤ := WithZero.log (Valued.v x₀) with hk₀
  have hvx₀ : Valued.v x₀ = WithZero.exp k₀ := by
    rw [hk₀, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx₀0)]
  refine ⟨k₀ + m, fun a ha => ?_⟩

  set y : v.adicCompletion ℚ := ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x₀ with hy
  have hva : ∃ ka : ℤ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp ka :=
    ⟨WithZero.log (Valued.v (a : v.adicCompletion ℚ)), by rw [WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)]⟩
  obtain ⟨ka, hka⟩ := hva
  have hka' : k₀ + m < ka := by
    have := ha; rw [hka] at this; exact WithZero.exp_lt_exp.mp this
  have hysmall : Valued.v y ≤ WithZero.exp (-(m : ℤ)) := by
    rw [hy, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hka, hvx₀, ← WithZero.exp_neg, ← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by omega)

  have hn : (upperUnipotent3 y 0 0 : LocalGL3 v) ∈ LocalZetaRational.principalCongruence3 v m := by
    have hy1 : Valued.v y ≤ 1 := hysmall.trans (WithZero.exp_le_exp.mpr (by omega) |>.trans_eq WithZero.exp_zero)
    refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> (try simp) <;> first | exact hy1 | (simpa using hy1)
    · intro i j
      change Valued.v ((upperUnipotent3 y 0 0 : LocalGL3 v).inv i j) ≤ 1
      fin_cases i <;> fin_cases j <;> (try simp [upperUnipotent3]) <;> first | exact hy1 | (simpa using hy1) | (simpa [Valuation.map_neg] using hy1)
    · intro i j
      fin_cases i <;> fin_cases j <;> (try simp) <;> first | exact hysmall | (simpa using hysmall) | (simpa using hy1)
  have hmem : g⁻¹ * upperUnipotent3 y 0 0 * g ∈ Uv := by
    have := hm hn
    simp only [U', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    obtain ⟨k', hk', hkeq⟩ := this
    have : k' = g⁻¹ * upperUnipotent3 y 0 0 * g := by
      rw [← hkeq]; group
    rw [← this]; exact hk'

  have h1 : W (iotaGL (diagUnitGL2 a) * g) = W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 y 0 0 * g)) := by
    have := hUW _ hmem (iotaGL (diagUnitGL2 a) * g)
    rw [show iotaGL (diagUnitGL2 a) * g * (g⁻¹ * upperUnipotent3 y 0 0 * g) =
      iotaGL (diagUnitGL2 a) * (upperUnipotent3 y 0 0 * g) by simp only [mul_assoc, mul_inv_cancel_left]] at this
    exact this.symm
  have hay : (a : v.adicCompletion ℚ) * y = x₀ := by
    rw [hy, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h2 : W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 y 0 0 * g)) = ψv x₀ * W (iotaGL (diagUnitGL2 a) * g) := by
    rw [← mul_assoc, Ws31.TS.torus_mul_upperUnipotent3 v a y 0 0, mul_zero, mul_assoc, hW, add_zero, hay]
  have h3 : (1 - ψv x₀) * W (iotaGL (diagUnitGL2 a) * g) = 0 := by
    rw [sub_mul, one_mul, ← h2, ← h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hx₀))

end S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn (solution)
