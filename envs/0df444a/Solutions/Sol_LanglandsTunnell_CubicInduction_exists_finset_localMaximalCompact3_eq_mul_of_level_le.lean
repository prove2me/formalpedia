-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finset_localMaximalCompact3_eq_mul_of_level_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ad61b8e0-3fa3-5291-9316-085499672cd9

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3Entry valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 isClopen_setOf_valued_sub_le isCompact_localMaximalCompact3"
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

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (n m : ℕ) (hnm : n ≤ m) (hm : 1 ≤ m) :
    ∃ S : Finset (LocalGL3 v),
      (∀ s ∈ S, s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ ∀ i j : Fin 3,
        Valued.v (gl3Entry v s i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        ∃! s, s ∈ S ∧ ∃ κ : LocalGL3 v,
          (∀ i j : Fin 3,
            Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
              ≤ WithZero.exp (-(m : ℤ))) ∧
          k = s * κ := by
  classical
  have hcont : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v => gl3Entry v k i j := fun i j => by
    unfold gl3Entry
    exact Units.continuous_val.matrix_elem i j
  have hclopen : ∀ l : ℕ, IsClopen {k : LocalGL3 v | IsLevel3 v l k} := by
    intro l
    have hset : {k : LocalGL3 v | IsLevel3 v l k} = ⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun k : LocalGL3 v => gl3Entry v k i j) ⁻¹'
          {x : v.adicCompletion ℚ |
            Valued.v (x - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(l : ℤ))} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IsLevel3]
    rw [hset]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      (isClopen_setOf_valued_sub_le v _ _).preimage (hcont i j)
  have hLn : IsCompact {k : LocalGL3 v | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v n k} := by
    have hset : {k : LocalGL3 v | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v n k} =
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) ∩
          {k : LocalGL3 v | IsLevel3 v n k} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe]
    rw [hset]
    exact (isCompact_localMaximalCompact3 v).inter_right (hclopen n).isClosed
  have hcover : {k : LocalGL3 v | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v n k} ⊆
      ⋃ s ∈ {k : LocalGL3 v | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v n k},
        (fun κ : LocalGL3 v => s * κ) '' {κ : LocalGL3 v | IsLevel3 v m κ} := by
    intro k hk
    exact Set.mem_iUnion₂.2 ⟨k, hk, 1, isLevel3_one v m, mul_one k⟩
  obtain ⟨t, htsub, htfin, htcover⟩ := hLn.elim_finite_subcover_image
    (fun s _ => (isOpenMap_mul_left s) _ (hclopen m).isOpen) hcover
  refine ⟨(htfin.toFinset.image (QuotientGroup.mk : LocalGL3 v → LocalGL3 v ⧸ levelSubgroup3 v m)).image
    Quotient.out, ?_, ?_⟩
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hq
    have hs₀Ln := htsub (htfin.mem_toFinset.1 hs₀)
    have hrel : s₀⁻¹ * (QuotientGroup.mk s₀ : LocalGL3 v ⧸ levelSubgroup3 v m).out ∈ levelSubgroup3 v m :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk s₀ : LocalGL3 v ⧸ levelSubgroup3 v m)).symm
    have hrelK := mem_localMaximalCompact3_of_mem_levelSubgroup3 v hrel
    have hK := (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hs₀Ln.1 hrelK
    have hlev := isLevel3_mul v hs₀Ln.2 (isLevel3_of_le v hnm (isLevel3_of_mem_levelSubgroup3 v hrel)) hrelK
    rw [mul_inv_cancel_left] at hK hlev
    exact ⟨hK, hlev⟩
  · intro k hkK hkn
    obtain ⟨s, hst, κ, hκ, hsk⟩ := Set.mem_iUnion₂.1 (htcover ⟨hkK, hkn⟩)
    have hκH : κ ∈ levelSubgroup3 v m := mem_levelSubgroup3_of_isLevel3 v hm hκ
    have hsq : (QuotientGroup.mk s : LocalGL3 v ⧸ levelSubgroup3 v m) = QuotientGroup.mk k := by
      rw [QuotientGroup.eq, ← hsk, inv_mul_cancel_left]
      exact hκH
    have hout : ((QuotientGroup.mk k : LocalGL3 v ⧸ levelSubgroup3 v m).out)⁻¹ * k ∈ levelSubgroup3 v m :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk k : LocalGL3 v ⧸ levelSubgroup3 v m))
    refine ⟨(QuotientGroup.mk k : LocalGL3 v ⧸ levelSubgroup3 v m).out,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_image.2 ⟨s, htfin.mem_toFinset.2 hst, hsq⟩, rfl⟩,
        _, isLevel3_of_mem_levelSubgroup3 v hout, (mul_inv_cancel_left _ k).symm⟩, ?_⟩
    rintro s₂ ⟨hs₂, κ₂, hκ₂, rfl⟩
    obtain ⟨q₂, _, rfl⟩ := Finset.mem_image.1 hs₂
    rw [QuotientGroup.mk_mul_of_mem _ (mem_levelSubgroup3_of_isLevel3 v hm hκ₂), QuotientGroup.out_eq']

end S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le (solution)
