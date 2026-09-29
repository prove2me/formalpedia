-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cdd75599-aec8-547e-abe1-5b69387516f6

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry gl3AmbientRightTranslate valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 finiteDimensional_fixedPoints_principalSeries3 exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 exists_finset_localMaximalCompact3_eq_mul_of_level_le"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def IsLevel3 (m : ℕ) (κ : LocalGL3 v) : Prop :=
  ∀ i j : Fin 3,
    Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))

private theorem isLevel3_iff (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_iff_sub_one (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j) ≤ WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_one (m : ℕ) : IsLevel3 v m 1 := by
  intro i j
  simp only [gl3Entry, Units.val_one, sub_self, map_zero]
  exact zero_le

private theorem valued_coe_apply_le_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 :=
  hk.1 i j

private theorem isLevel3_mul {m : ℕ} {a b : LocalGL3 v} (ha : IsLevel3 v m a) (hb : IsLevel3 v m b)
    (hbK : b ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : IsLevel3 v m (a * b) := by
  rw [isLevel3_iff_sub_one] at ha hb ⊢
  intro i j
  have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) +
        ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul]
    abel
  rw [hid, Matrix.add_apply]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hb i j))
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hbK.1 l j)

private theorem
    isLevel3_inv {m : ℕ} {a : LocalGL3 v} (ha : IsLevel3 v m a) (haK : a ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v m a⁻¹ := by
  rw [isLevel3_iff_sub_one] at ha ⊢
  intro i j
  have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (1 - (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [sub_mul, one_mul, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ?_) (fun l => haK.2 l j)
  rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
  exact ha i l

private def levelSubgroup3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k}
  one_mem' := ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, isLevel3_one v m⟩
  mul_mem' := fun {_ _} ⟨haK, ha⟩ ⟨hbK, hb⟩ =>
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem haK hbK, isLevel3_mul v ha hb hbK⟩
  inv_mem' := fun {_} ⟨haK, ha⟩ => ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem haK, isLevel3_inv v ha haK⟩

private theorem mem_levelSubgroup3_iff (m : ℕ) (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k :=
  Iff.rfl

private theorem mem_localMaximalCompact3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  hk.1

private theorem
    isLevel3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) : IsLevel3 v m k :=
  hk.2

private theorem mem_levelSubgroup3_of_eq_mul {m : ℕ} {s k κ : LocalGL3 v} (hs : s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hκ : IsLevel3 v m κ) (h : k = s * κ) : κ ∈ levelSubgroup3 v m := by
  refine (mem_levelSubgroup3_iff v m κ).2 ⟨?_, hκ⟩
  have : κ = s⁻¹ * k := by rw [h, inv_mul_cancel_left]
  rw [this]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hs) hk

private theorem isLevel3_of_le {n m : ℕ} (hnm : n ≤ m) {k : LocalGL3 v} (hk : IsLevel3 v m k) : IsLevel3 v n k := by
  intro i j
  refine le_trans (hk i j) ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem levelSubgroup3_le_of_le {n m : ℕ} (hnm : n ≤ m) : levelSubgroup3 v m ≤ levelSubgroup3 v n :=
  fun k hk => (mem_levelSubgroup3_iff v n k).2
    ⟨((mem_levelSubgroup3_iff v m k).1 hk).1, isLevel3_of_le v hnm ((mem_levelSubgroup3_iff v m k).1 hk).2⟩

private theorem isLevel3_zero_of_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v 0 k := by
  intro i j
  have h1 : WithZero.exp (-((0 : ℕ) : ℤ)) = 1 := by simp
  rw [h1]
  exact le_trans (Valuation.map_sub _ _ _) (max_le (hk.1 i j) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))

private theorem levelSubgroup3_zero : levelSubgroup3 v 0 = localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  ext k
  exact ⟨fun hk => ((mem_levelSubgroup3_iff v 0 k).1 hk).1,
    fun hk => (mem_levelSubgroup3_iff v 0 k).2 ⟨hk, isLevel3_zero_of_mem_localMaximalCompact3 v hk⟩⟩

private theorem mem_levelSubgroup3_zero_iff (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v 0 ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [levelSubgroup3_zero]

private theorem valued_mul_apply_le3_right {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ 1) (hb : ∀ l, Valued.v (b l j) ≤ C) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem isLevel3_conj {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : IsLevel3 v m κ) : IsLevel3 v m (k * κ * k⁻¹) := by
  rw [isLevel3_iff_sub_one] at hκ ⊢
  intro i j
  have hid : ((k * κ * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
          ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    rw [Units.val_mul, Units.val_mul, sub_mul, one_mul, mul_sub, ← mul_assoc, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3_right v (fun l => hk.1 i l) (fun l => ?_)
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l' => hκ l l') (fun l' => hk.2 l' j)

private theorem mul_mul_inv_mem_levelSubgroup3 {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : κ ∈ levelSubgroup3 v m) : k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  (mem_levelSubgroup3_iff v m _).2
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hκ))
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk),
      isLevel3_conj v hk (isLevel3_of_mem_levelSubgroup3 v hκ)⟩

private theorem valued_mul_apply_le3_mul {C C' : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ C') :
    Valued.v ((a * b) i j) ≤ C * C' := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C * C' := fun l => by
    rw [map_mul]
    exact mul_le_mul' (ha l) (hb l)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem le_one_of_le_max_mul {M e : WithZero (Multiplicative ℤ)} (he : e < 1) (h : M ≤ max 1 (M * e)) :
    M ≤ 1 := by
  rcases le_or_gt M 1 with hM | hM
  · exact hM
  · exfalso
    have h' : M ≤ M * e := (le_max_iff.1 h).resolve_left (not_le.2 hM)
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 (zero_lt_one.trans hM).ne'
    rcases eq_or_ne e 0 with rfl | he0
    · rw [mul_zero] at h'
      exact absurd h' (not_le.2 (WithZero.zero_lt_coe u))
    · obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 he0
      rw [← WithZero.coe_mul, WithZero.coe_le_coe] at h'
      rw [← WithZero.coe_one, WithZero.coe_lt_coe] at he
      exact absurd ((le_mul_iff_one_le_right' _).1 h') (not_le.2 he)

private theorem exp_neg_one_lt_one : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem mem_localMaximalCompact3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h1 := isLevel3_of_le v hn hk
  rw [isLevel3_iff_sub_one] at h1
  refine ⟨fun i j => ?_, ?_⟩
  · have hsplit : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j +
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
      simp
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (le_trans (h1 i j) (exp_neg_one_lt_one).le) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))
  · have hid : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        1 - ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [mul_sub, mul_one, Units.inv_mul, sub_sub_cancel]
    have hle : ∀ p : Fin 3 × Fin 3,
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2) ≤
          Finset.univ.sup fun q : Fin 3 × Fin 3 =>
            Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2) :=
      fun p => Finset.le_sup (f := fun q : Fin 3 × Fin 3 =>
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2)) (Finset.mem_univ p)
    have hbound : ∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        max 1 ((Finset.univ.sup fun p : Fin 3 × Fin 3 =>
          Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2)) *
            WithZero.exp (-((1 : ℕ) : ℤ))) := by
      intro i j
      conv_lhs => rw [hid]
      rw [Matrix.sub_apply]
      refine le_trans (Valuation.map_sub _ _ _) (max_le_max (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j) ?_)
      exact valued_mul_apply_le3_mul v (fun l => hle (i, l)) (fun l => h1 l j)
    have hM := le_one_of_le_max_mul (exp_neg_one_lt_one) (Finset.sup_le fun (p : Fin 3 × Fin 3) _ => hbound p.1 p.2)
    exact fun i j => le_trans (hle (i, j)) hM

private theorem mem_levelSubgroup3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ levelSubgroup3 v n :=
  (mem_levelSubgroup3_iff v n k).2 ⟨mem_localMaximalCompact3_of_isLevel3 v hn hk, hk⟩

section Transversal

variable {G : Type*} [Group G]

private def IsTransversal (H H' : Subgroup G) (S : Finset G) : Prop :=
  (∀ s ∈ S, s ∈ H) ∧
    ∀ k ∈ H, ∃! s, s ∈ S ∧ ∃ κ ∈ H', k = s * κ

private theorem sum_eq_of_isTransversal {H H' : Subgroup G} {S S' : Finset G} (hS : IsTransversal H H' S)
    (hS' : IsTransversal H H' S') {φ : G → ℂ}
    (hφ : ∀ s, ∀ κ ∈ H', φ (s * κ) = φ s) :
    ∑ s ∈ S, φ s = ∑ s ∈ S', φ s := by

  have hmatch : ∀ s ∈ S, ∃ s', s' ∈ S' ∧ ∃ κ ∈ H', s = s' * κ :=
    fun s hs => (hS'.2 s (hS.1 s hs)).exists
  refine Finset.sum_bij (fun s hs => (hmatch s hs).choose) (fun s hs => (hmatch s hs).choose_spec.1) ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ heq
    obtain ⟨κ₁, hκ₁, h₁⟩ := (hmatch s₁ hs₁).choose_spec.2
    obtain ⟨κ₂, hκ₂, h₂⟩ := (hmatch s₂ hs₂).choose_spec.2

    have hu := hS.2 _ (hS'.1 _ (hmatch s₁ hs₁).choose_spec.1)
    exact hu.unique ⟨hs₁, κ₁⁻¹, H'.inv_mem hκ₁, eq_mul_inv_of_mul_eq h₁.symm⟩
      ⟨hs₂, κ₂⁻¹, H'.inv_mem hκ₂, heq.trans (eq_mul_inv_of_mul_eq h₂.symm)⟩
  · intro s' hs'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, -⟩ := hS.2 s' (hS'.1 s' hs')
    refine ⟨s, hs, ?_⟩
    obtain ⟨κ', hκ', h'⟩ := (hmatch s hs).choose_spec.2

    refine (hS'.2 s' (hS'.1 s' hs')).unique
      ⟨(hmatch s hs).choose_spec.1, κ' * κ, H'.mul_mem hκ' hκ, ?_⟩
      ⟨hs', 1, H'.one_mem, (mul_one s').symm⟩
    rw [hsκ, ← mul_assoc, ← h']
  · intro s hs
    obtain ⟨κ, hκ, h⟩ := (hmatch s hs).choose_spec.2
    exact (congrArg φ h).trans (hφ _ κ hκ)

private theorem
    isTransversal_image_mul [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S) {k : G}
    (hk : k ∈ H) : IsTransversal H H' (S.image (fun s => k * s)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.mul_mem hk (hS.1 s hs)
  · intro k' hk'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ :=
      hS.2 (k⁻¹ * k') (H.mul_mem (H.inv_mem hk) hk')
    refine ⟨k * s, ⟨Finset.mem_image_of_mem _ hs, κ, hκ, ?_⟩, ?_⟩
    · rw [mul_assoc, ← hsκ, mul_inv_cancel_left]
    · rintro t ⟨ht, κ', hκ', hκ'eq⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht
      have : s' = s := huniq s' ⟨hs', κ', hκ', by rw [hκ'eq, mul_assoc, inv_mul_cancel_left]⟩
      rw [this]

private theorem isTransversal_image_inv [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    (hN : ∀ k ∈ H, ∀ κ ∈ H', k * κ * k⁻¹ ∈ H') :
    IsTransversal H H' (S.image (fun s => s⁻¹)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.inv_mem (hS.1 s hs)
  · intro k hk
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ := hS.2 k⁻¹ (H.inv_mem hk)
    refine ⟨s⁻¹, ⟨Finset.mem_image_of_mem _ hs, _,
      hN s (hS.1 s hs) _ (H'.inv_mem hκ), ?_⟩, ?_⟩
    · rw [← inv_inv k, hsκ]
      group
    · rintro t ⟨ht, κ', hκ', hk'⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
      have hus : u = s :=
        huniq u ⟨hu, _, hN u⁻¹ (H.inv_mem (hS.1 u hu)) _ (H'.inv_mem hκ'), by rw [hk']; group⟩
      rw [hus]

end Transversal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def levelAvg (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun g => (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s)

private theorem levelAvg_apply (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    levelAvg v S f g = (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s) :=
  rfl

private theorem levelAvg_eq_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S S' : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) (hS' : IsTransversal H H' S') {f : LocalGL3 v → ℂ}
    (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) :
    levelAvg v S f = levelAvg v S' f := by
  have hcard : (S.card : ℂ) = S'.card := by
    have h := sum_eq_of_isTransversal hS hS' (φ := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    simpa using h
  funext g
  rw [levelAvg_apply, levelAvg_apply, hcard]
  congr 1
  exact sum_eq_of_isTransversal hS hS' (φ := fun s => f (g * s))
    (fun s κ hκ => by simp only [← mul_assoc]; exact hf κ hκ (g * s))

private theorem levelAvg_mul_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) {k : LocalGL3 v}
    (hk : k ∈ H) (g : LocalGL3 v) : levelAvg v S f (g * k) = levelAvg v S f g := by
  classical
  have himg : levelAvg v (S.image (fun s => k * s)) f g = levelAvg v S f (g * k) := by
    rw [levelAvg_apply, levelAvg_apply, Finset.card_image_of_injective _ (mul_right_injective k),
      Finset.sum_image (fun _ _ _ _ h => mul_right_injective k h)]
    simp only [mul_assoc]
  rw [← himg, levelAvg_eq_of_isTransversal v (isTransversal_image_mul hS hk) hS hf]

private abbrev IsTransversal3 (n m : ℕ) (S : Finset (LocalGL3 v)) : Prop :=
  IsTransversal (levelSubgroup3 v n) (levelSubgroup3 v m) S

private theorem levelSubgroup3_normalizes (n m : ℕ) :
    ∀ k ∈ levelSubgroup3 v n, ∀ κ ∈ levelSubgroup3 v m, k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  fun _ hk _ hκ => mul_mul_inv_mem_levelSubgroup3 v (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hk) hκ

private theorem levelAvg_eq_smul_sum (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) :
    levelAvg v S f = (S.card : ℂ)⁻¹ • ∑ s ∈ S, gl3AmbientRightTranslate (R := ℂ) s f := by
  funext g
  simp [levelAvg, Finset.sum_apply]

private theorem levelAvg_mem_principalSeries3 (S : Finset (LocalGL3 v)) {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : levelAvg v S f ∈ principalSeries3 v χ := by
  rw [levelAvg_eq_smul_sum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun s _ => rightTranslate_mem_principalSeries3 hf s))

private noncomputable def levelAvgLin (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (S.card : ℂ)⁻¹ • ∑ s ∈ S,
    (gl3AmbientRightTranslate (R := ℂ) s).restrict (p := principalSeries3 v χ) (q := principalSeries3 v χ)
      (fun _ hf => rightTranslate_mem_principalSeries3 hf s)

private theorem coe_levelAvgLin_apply (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    ((levelAvgLin v S χ f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = levelAvg v S f := by
  rw [levelAvg_eq_smul_sum]
  simp [levelAvgLin, LinearMap.sum_apply]

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry gl3AmbientRightTranslate valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 finiteDimensional_fixedPoints_principalSeries3 exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 exists_finset_localMaximalCompact3_eq_mul_of_level_le"
namespace UnitaryComplement
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate.LanglandsTunnell.CubicInduction"

private theorem exists_mem_add_forall_apply_eq_zero_of_finrank_eq
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (hherm : ∀ x y : E, B x y = (starRingEnd ℂ) (B y x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < (B x x).re) (n : ℕ) :
    ∀ (K : Submodule ℂ E), Module.finrank ℂ ↥K = n →
      ∀ x : E, ∃ a ∈ K, ∃ b : E, (∀ k ∈ K, B k b = 0) ∧ x = a + b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hK x
    by_cases hbot : K = ⊥
    · refine ⟨0, K.zero_mem, x, fun k hk => ?_, (zero_add x).symm⟩
      rw [hbot, Submodule.mem_bot] at hk
      rw [hk, map_zero, LinearMap.zero_apply]
    · obtain ⟨k₀, hk₀K, hk₀⟩ := (Submodule.ne_bot_iff K).mp hbot
      have hB00 : B k₀ k₀ ≠ 0 := fun h => by
        have h1 := hpos k₀ hk₀
        rw [h, Complex.zero_re] at h1
        exact lt_irrefl 0 h1

      let K₁ : Submodule ℂ E := K ⊓ LinearMap.ker (B.flip k₀)
      have hmem₁ : ∀ k, k ∈ K₁ ↔ k ∈ K ∧ B k k₀ = 0 := fun k => by
        simp only [K₁, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.flip_apply]
      have hlt : K₁ < K := by
        refine SetLike.lt_iff_le_and_exists.mpr ⟨inf_le_left, k₀, hk₀K, fun h => hB00 ((hmem₁ k₀).mp h).2⟩
      have hdim : Module.finrank ℂ ↥K₁ < n := hK ▸ Submodule.finrank_lt_finrank_of_lt hlt

      set μ : ℂ := (starRingEnd ℂ) (B k₀ x / B k₀ k₀) with hμ
      have hx₁ : B k₀ (x - μ • k₀) = 0 := by
        rw [map_sub, LinearMap.map_smulₛₗ, hμ, starRingEnd_self_apply, smul_eq_mul, div_mul_cancel₀ _ hB00, sub_self]
      obtain ⟨a₁, ha₁, b₁, hb₁, hxab⟩ := ih _ hdim K₁ rfl (x - μ • k₀)
      have ha₁K : a₁ ∈ K := ((hmem₁ a₁).mp ha₁).1
      have hb₁k₀ : B k₀ b₁ = 0 := by
        have hb : b₁ = (x - μ • k₀) - a₁ := eq_sub_of_add_eq' hxab.symm
        rw [hb, map_sub, hx₁, hherm k₀ a₁, ((hmem₁ a₁).mp ha₁).2, map_zero, sub_zero]
      refine ⟨a₁ + μ • k₀, K.add_mem ha₁K (K.smul_mem μ hk₀K), b₁, fun k hk => ?_, ?_⟩
      ·
        set ν : ℂ := B k k₀ / B k₀ k₀ with hν
        have hk₁ : k - ν • k₀ ∈ K₁ := by
          refine (hmem₁ _).mpr ⟨K.sub_mem hk (K.smul_mem ν hk₀K), ?_⟩
          rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hν,
            div_mul_cancel₀ _ hB00, sub_self]
        have hsplit : k = ν • k₀ + (k - ν • k₀) := (add_sub_cancel (ν • k₀) k).symm
        rw [hsplit, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb₁k₀, mul_zero,
          zero_add, hb₁ _ hk₁]
      · calc x = (x - μ • k₀) + μ • k₀ := (sub_add_cancel x (μ • k₀)).symm
          _ = a₁ + b₁ + μ • k₀ := by rw [hxab]
          _ = a₁ + μ • k₀ + b₁ := add_right_comm a₁ b₁ (μ • k₀)

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private def fixedLevel (n : ℕ) : Submodule ℂ (LocalGL3 v → ℂ) :=
  principalSeries3 v χ ⊓
    ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))},
      LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id)

private theorem mem_fixedLevel_iff (n : ℕ) (f : LocalGL3 v → ℂ) :
    f ∈ fixedLevel v χ n ↔ f ∈ principalSeries3 v χ ∧
      ∀ k : LocalGL3 v, IsLevel3 v n k → gl3AmbientRightTranslate (R := ℂ) k f = f := by
  simp only [fixedLevel, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, Set.mem_setOf_eq, IsLevel3]

private theorem fixedLevel_le (n : ℕ) : fixedLevel v χ n ≤ principalSeries3 v χ := inf_le_left

private theorem finiteDimensional_fixedLevel (n : ℕ) : FiniteDimensional ℂ ↥(fixedLevel v χ n) :=
  finiteDimensional_fixedPoints_principalSeries3 v χ n

end LanglandsTunnell.CubicInduction.UnitaryComplement

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.UnitaryComplement in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (U : Submodule ℂ (LocalGL3 v → ℂ)) (hU : U ≤ principalSeries3 v χ)
    (hstab : ∀ g : LocalGL3 v, U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) g)) :
    ∃ U' : Submodule ℂ (LocalGL3 v → ℂ), U' ≤ principalSeries3 v χ ∧
      (∀ g : LocalGL3 v, U' ≤ U'.comap (gl3AmbientRightTranslate (R := ℂ) g)) ∧
      U ⊓ U' = ⊥ ∧ U ⊔ U' = principalSeries3 v χ := by
  have hform := exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one v χ hunit
  have hunif : ∀ f : LocalGL3 v → ℂ, f ∈ principalSeries3 v χ →
      ∃ n : ℕ, ∀ k : LocalGL3 v, IsLevel3 v n k → gl3AmbientRightTranslate (R := ℂ) k f = f := by
    intro f hf
    obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
    exact ⟨n, fun k hk => hn k ((isLevel3_iff v n k).1 hk)⟩
  have htrans : ∀ n m : ℕ, n ≤ m → 1 ≤ m → ∃ S : Finset (LocalGL3 v), IsTransversal3 v n m S := by
    intro n m hnm hm
    obtain ⟨S, hSmem, hSuniq⟩ := exists_finset_localMaximalCompact3_eq_mul_of_level_le v n m hnm hm
    refine ⟨S, ?_⟩
    show (∀ s ∈ S, s ∈ levelSubgroup3 v n) ∧
      ∀ k ∈ levelSubgroup3 v n, ∃! s, s ∈ S ∧ ∃ κ ∈ levelSubgroup3 v m, k = s * κ
    refine ⟨fun s hs => (mem_levelSubgroup3_iff v n s).2 ⟨(hSmem s hs).1, (isLevel3_iff v n s).2 (hSmem s hs).2⟩,
      fun k hk => ?_⟩
    obtain ⟨hkK, hkn⟩ := (mem_levelSubgroup3_iff v n k).1 hk
    obtain ⟨s, ⟨hsS, κ, hκm, hksκ⟩, huniq⟩ := hSuniq k hkK ((isLevel3_iff v n k).1 hkn)
    have hκK : κ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
      have hκ : κ = s⁻¹ * k := by rw [hksκ, inv_mul_cancel_left]
      rw [hκ]
      exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem (hSmem s hsS).1) hkK
    refine ⟨s, ⟨hsS, κ, (mem_levelSubgroup3_iff v m κ).2 ⟨hκK, (isLevel3_iff v m κ).2 hκm⟩, hksκ⟩, ?_⟩
    rintro s' ⟨hs'S, κ', hκ', hks'κ'⟩
    exact huniq s' ⟨hs'S, κ', (isLevel3_iff v m κ').1 ((mem_levelSubgroup3_iff v m κ').1 hκ').2, hks'κ'⟩
  classical
  obtain ⟨B, hherm, hpos, hinv⟩ := hform

  let UP : Submodule ℂ ↥(principalSeries3 v χ) := U.comap (principalSeries3 v χ).subtype
  let OP : Submodule ℂ ↥(principalSeries3 v χ) := UP.orthogonalBilin B
  have hUP : ∀ u : ↥(principalSeries3 v χ), u ∈ UP ↔ (u : LocalGL3 v → ℂ) ∈ U := fun u => Submodule.mem_comap
  have hOP : ∀ f : ↥(principalSeries3 v χ), f ∈ OP ↔ ∀ u ∈ UP, B u f = 0 := fun f => by
    rw [Submodule.mem_orthogonalBilin_iff]

  have hback : ∀ (g : LocalGL3 v) (u : ↥(principalSeries3 v χ)),
      (⟨gl3AmbientRightTranslate (R := ℂ) g (gl3AmbientRightTranslate (R := ℂ) g⁻¹ (u : LocalGL3 v → ℂ)),
        rightTranslate_mem_principalSeries3 (rightTranslate_mem_principalSeries3 u.2 g⁻¹) g⟩ :
          ↥(principalSeries3 v χ)) = u := fun g u =>
    Subtype.ext (funext fun x => by
      show (u : LocalGL3 v → ℂ) (x * g * g⁻¹) = (u : LocalGL3 v → ℂ) x
      rw [mul_inv_cancel_right])
  refine ⟨OP.map (principalSeries3 v χ).subtype, Submodule.map_subtype_le _ _, ?_, ?_, ?_⟩
  ·
    intro g x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr
      ⟨⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩, ?_, rfl⟩)
    rw [hOP] at hf ⊢
    intro u hu
    have hu' : (⟨gl3AmbientRightTranslate (R := ℂ) g⁻¹ (u : LocalGL3 v → ℂ),
        rightTranslate_mem_principalSeries3 u.2 g⁻¹⟩ : ↥(principalSeries3 v χ)) ∈ UP :=
      (hUP _).mpr (Submodule.mem_comap.mp (hstab g⁻¹ ((hUP u).mp hu)))
    have h0 := hf _ hu'
    have h1 := hinv g ⟨gl3AmbientRightTranslate (R := ℂ) g⁻¹ (u : LocalGL3 v → ℂ),
      rightTranslate_mem_principalSeries3 u.2 g⁻¹⟩ f
    rw [hback g u] at h1
    rw [h1, h0]
  ·
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    obtain ⟨hxU, hxO⟩ := Submodule.mem_inf.mp hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxO
    rw [hOP] at hf
    have h0 : B f f = 0 := hf f ((hUP f).mpr hxU)
    by_contra hne
    have hne' : f ≠ 0 := fun h => hne (by rw [h]; rfl)
    have h1 := hpos f hne'
    rw [h0, Complex.zero_re] at h1
    exact lt_irrefl 0 h1
  ·
    apply le_antisymm (sup_le hU (Submodule.map_subtype_le _ _))
    intro f hfP
    obtain ⟨n₀, hn₀⟩ := hunif f hfP
    obtain ⟨n, h1n, hfix⟩ : ∃ n : ℕ, 1 ≤ n ∧
        ∀ k : LocalGL3 v, IsLevel3 v n k → gl3AmbientRightTranslate (R := ℂ) k f = f :=
      ⟨n₀ + 1, Nat.le_add_left 1 n₀, fun k hk => hn₀ k (isLevel3_of_le v (Nat.le_succ n₀) hk)⟩
    have hfW : f ∈ fixedLevel v χ n := (mem_fixedLevel_iff v χ n f).mpr ⟨hfP, hfix⟩
    haveI := finiteDimensional_fixedLevel v χ n

    let ι : ↥(fixedLevel v χ n) →ₗ[ℂ] ↥(principalSeries3 v χ) := Submodule.inclusion (fixedLevel_le v χ n)
    let B' : ↥(fixedLevel v χ n) →ₗ[ℂ] ↥(fixedLevel v χ n) →ₗ⋆[ℂ] ℂ :=
      LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (ι x) (ι y))
        (fun x₁ x₂ y => by
          show B (ι (x₁ + x₂)) (ι y) = B (ι x₁) (ι y) + B (ι x₂) (ι y)
          rw [LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply])
        (fun c x y => by
          show B (ι (c • x)) (ι y) = (RingHom.id ℂ) c • B (ι x) (ι y)
          rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, RingHom.id_apply])
        (fun x y₁ y₂ => by
          show B (ι x) (ι (y₁ + y₂)) = B (ι x) (ι y₁) + B (ι x) (ι y₂)
          rw [LinearMap.map_add, LinearMap.map_add])
        (fun c x y => by
          show B (ι x) (ι (c • y)) = (starRingEnd ℂ) c • B (ι x) (ι y)
          rw [LinearMap.map_smul, LinearMap.map_smulₛₗ])
    have hB' : ∀ x y, B' x y = B (ι x) (ι y) := fun _ _ => rfl
    have hherm' : ∀ x y, B' x y = (starRingEnd ℂ) (B' y x) := fun x y => by rw [hB', hB', hherm]
    have hpos' : ∀ x, x ≠ 0 → 0 < (B' x x).re := fun x hx => by
      rw [hB']
      exact hpos (ι x) (fun h => hx (Submodule.inclusion_injective _ (h.trans (map_zero ι).symm)))
    let KU : Submodule ℂ ↥(fixedLevel v χ n) := U.comap (fixedLevel v χ n).subtype
    obtain ⟨a, ha, b, horth, hab⟩ :=
      exists_mem_add_forall_apply_eq_zero_of_finrank_eq B' hherm' hpos' _ KU rfl ⟨f, hfW⟩
    have hfab : f = (a : LocalGL3 v → ℂ) + (b : LocalGL3 v → ℂ) := by
      have := congrArg Subtype.val hab
      exact this
    rw [hfab]
    refine Submodule.add_mem_sup (Submodule.mem_comap.mp ha) (Submodule.mem_map.mpr ⟨ι b, ?_, rfl⟩)

    rw [hOP]
    intro u hu
    obtain ⟨m₀, hm₀⟩ := hunif u u.2
    obtain ⟨m, hnm, h1m, hm₀m⟩ : ∃ m : ℕ, n ≤ m ∧ 1 ≤ m ∧ m₀ ≤ m :=
      ⟨m₀ + n, Nat.le_add_left n m₀, le_trans h1n (Nat.le_add_left n m₀), Nat.le_add_right m₀ n⟩
    obtain ⟨S, hS⟩ := htrans n m hnm h1m
    have hbfix : ∀ k : LocalGL3 v, IsLevel3 v n k →
        gl3AmbientRightTranslate (R := ℂ) k ((ι b : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = ι b :=
      ((mem_fixedLevel_iff v χ n _).mp b.2).2

    have hterm : ∀ t ∈ S, B ⟨gl3AmbientRightTranslate (R := ℂ) t (u : LocalGL3 v → ℂ),
        rightTranslate_mem_principalSeries3 u.2 t⟩ (ι b) = B u (ι b) := fun t ht => by
      have htn : IsLevel3 v n t := ((mem_levelSubgroup3_iff v n t).mp (hS.1 t ht)).2
      have hbt : (⟨gl3AmbientRightTranslate (R := ℂ) t ((ι b : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ),
          rightTranslate_mem_principalSeries3 (ι b).2 t⟩ : ↥(principalSeries3 v χ)) = ι b :=
        Subtype.ext (hbfix t htn)
      have h := hinv t u (ι b)
      rw [hbt] at h
      exact h

    have huP : (u : LocalGL3 v → ℂ) ∈ principalSeries3 v χ := u.2
    let e : ↥(principalSeries3 v χ) := ⟨levelAvg v S (u : LocalGL3 v → ℂ), levelAvg_mem_principalSeries3 v S huP⟩
    have hcard : (S.card : ℂ) ≠ 0 := by
      obtain ⟨s, ⟨hs, _⟩, _⟩ := hS.2 1 (levelSubgroup3 v n).one_mem
      exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨s, hs⟩).ne'
    have he_sum : e = (S.card : ℂ)⁻¹ • ∑ t ∈ S, (⟨gl3AmbientRightTranslate (R := ℂ) t (u : LocalGL3 v → ℂ),
        rightTranslate_mem_principalSeries3 u.2 t⟩ : ↥(principalSeries3 v χ)) := by
      refine Subtype.ext ?_
      rw [Submodule.coe_smul, Submodule.coe_sum]
      exact levelAvg_eq_smul_sum v S (u : LocalGL3 v → ℂ)
    have hBe : B e (ι b) = B u (ι b) := by
      rw [he_sum, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm,
        Finset.sum_const, nsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

    have hu_m : ∀ κ ∈ levelSubgroup3 v m, ∀ g : LocalGL3 v, (u : LocalGL3 v → ℂ) (g * κ) = (u : LocalGL3 v → ℂ) g :=
      fun κ hκ g => by
        have h := hm₀ κ (isLevel3_of_le v hm₀m ((mem_levelSubgroup3_iff v m κ).mp hκ).2)
        exact congrFun h g
    have he_fix : ∀ k : LocalGL3 v, IsLevel3 v n k →
        gl3AmbientRightTranslate (R := ℂ) k (e : LocalGL3 v → ℂ) = e := fun k hk => by
      have hkK : k ∈ levelSubgroup3 v n := mem_levelSubgroup3_of_isLevel3 v h1n hk
      funext g
      exact levelAvg_mul_of_isTransversal v hS hu_m hkK g
    have he_U : (e : LocalGL3 v → ℂ) ∈ U := by
      show levelAvg v S (u : LocalGL3 v → ℂ) ∈ U
      rw [levelAvg_eq_smul_sum]
      exact U.smul_mem _ (U.sum_mem fun t _ => Submodule.mem_comap.mp (hstab t ((hUP u).mp hu)))
    have he_W : (e : LocalGL3 v → ℂ) ∈ fixedLevel v χ n := (mem_fixedLevel_iff v χ n _).mpr ⟨e.2, he_fix⟩
    have he_KU : (⟨(e : LocalGL3 v → ℂ), he_W⟩ : ↥(fixedLevel v χ n)) ∈ KU := Submodule.mem_comap.mpr he_U
    have h0 := horth _ he_KU
    rw [hB'] at h0
    have hιe : ι ⟨(e : LocalGL3 v → ℂ), he_W⟩ = e := Subtype.ext rfl
    rw [hιe, hBe] at h0
    exact h0

end

end S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate (solution)
