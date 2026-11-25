-- Prove2me | solution 1 for GlobalTheory.xClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:21.803496+00:00
-- url     : https://prove2.me/submissions/1dd2ccfe-ca3c-4e73-8139-607f8b5ea623

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom
import Theorems.Thm_GlobalTheory_xClasses_index
import Theorems.Thm_GlobalTheory_xClasses_mem
import Theorems.Thm_GlobalTheory_xClasses_denom
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : Ideal (𝓞 K)) (r : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), A ≠ ⊥ → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Matrix (Fin r) (Fin (r + 1)) K), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * A) ^ (r ^ 2) ∧ ∀ x : Matrix (Fin r) (Fin (r + 1)) K, (∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x a b) → xᴴ * Y.map (algebraMap (𝓞 K) K) + (Y.map (algebraMap (𝓞 K) K))ᴴ * x = 0 → ∃ x₀ ∈ reps, ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), (c.map (algebraMap (𝓞 K) K))ᴴ = -c.map (algebraMap (𝓞 K) K) ∧ x = x₀ + c.map (algebraMap (𝓞 K) K) * Y.map (algebraMap (𝓞 K) K) := by
  classical
  intro K _ _ _ A r Y b₀ hA hdet
  set f := b₀.succAbove with hf
  set φ := algebraMap (𝓞 K) K with hφ
  set D := (Y.submatrix id f).det with hD
  set I := Ideal.span {D} * A with hI
  set YK := Y.map φ with hYK
  have hφinj : Function.Injective φ := IsFractionRing.injective (𝓞 K) K
  have hc : ∀ u : 𝓞 K, (u : K) = φ u := fun u => rfl
  have hI0 : I ≠ ⊥ := by
    intro h0
    rcases mul_eq_zero.mp (show Ideal.span {D} * A = 0 from h0) with h1 | h1
    · exact hdet (Ideal.span_singleton_eq_bot.mp h1)
    · exact hA h1
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have haK : φ a ≠ 0 := fun h0 => ha0 (hφinj (h0.trans (map_zero φ).symm))

  let C : Matrix (Fin (r + 1)) (Fin r) K :=
    (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K).submatrix id f
  have hC : ∀ M : Matrix (Fin r) (Fin (r + 1)) K, M * C = M.submatrix id f := fun M => by
    simpa [C] using Matrix.mul_submatrix_one (Equiv.refl (Fin (r + 1))) f M
  have hYf : YK * C = (Y.submatrix id f).map φ := by
    rw [hC, hYK, Matrix.submatrix_map]
  have hdetYf : IsUnit (YK * C).det := by
    rw [hYf, show ((Y.submatrix id f).map φ).det = φ D from (RingHom.map_det φ _).symm]
    exact isUnit_iff_ne_zero.mpr (fun h0 => hdet (hφinj (h0.trans (map_zero φ).symm)))
  have hdetYfH : IsUnit (YK * C)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hdetYf))
  obtain ⟨Good, hGood⟩ : ∃ G : Matrix (Fin r) (Fin (r + 1)) K → Prop, ∀ x, G x ↔
      (∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * x p q) ∧ xᴴ * YK + YKᴴ * x = 0 :=
    ⟨_, fun _ => Iff.rfl⟩

  obtain ⟨Sx, hSx⟩ : ∃ Sx : Matrix (Fin r) (Fin (r + 1)) K → Matrix (Fin r) (Fin r) K,
      ∀ x, Good x → x = Sx x * YK ∧ (Sx x)ᴴ = -Sx x := by
    refine ⟨fun x => x * C * (YK * C)⁻¹, fun x hG => ?_⟩
    have hxY := ((hGood x).mp hG).2
    set Yf := YK * C with hYfdef
    set S := x * C * Yf⁻¹ with hS
    have hSYf : S * Yf = x * C := Matrix.nonsing_inv_mul_cancel_right _ _ hdetYf
    set P := x - S * YK with hP
    have hxP : x = S * YK + P := by rw [hP]; abel
    have hPC : P * C = 0 := by
      rw [hP, Matrix.sub_mul, Matrix.mul_assoc, ← hYfdef, hSYf, sub_self]
    have h1 : Cᴴ * xᴴ = Yfᴴ * Sᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hSYf]
    have h2 : Cᴴ * YKᴴ = Yfᴴ := by rw [← Matrix.conjTranspose_mul]
    have h3 : Yfᴴ * Sᴴ * YK + Yfᴴ * x = 0 := by
      have h0 : Cᴴ * (xᴴ * YK + YKᴴ * x) = 0 := by rw [hxY, Matrix.mul_zero]
      rwa [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2] at h0
    have h4 : Yfᴴ * ((Sᴴ + S) * YK + P) = 0 := by
      calc Yfᴴ * ((Sᴴ + S) * YK + P) = Yfᴴ * Sᴴ * YK + Yfᴴ * (S * YK + P) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
        _ = 0 := by rw [← hxP]; exact h3
    have h5 : (Sᴴ + S) * YK + P = 0 := by
      have h0 := congrArg (fun M => Yfᴴ⁻¹ * M) h4
      rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hdetYfH, Matrix.mul_zero] at h0
    have h6 : Sᴴ + S = 0 := by
      have h0 := congrArg (fun M => M * C * Yf⁻¹) h5
      rwa [Matrix.add_mul, hPC, add_zero, Matrix.mul_assoc ((Sᴴ + S)) YK C, ← hYfdef,
        Matrix.mul_nonsing_inv_cancel_right _ _ hdetYf, Matrix.zero_mul, Matrix.zero_mul] at h0
    have h7 : P = 0 := by rwa [h6, Matrix.zero_mul, zero_add] at h5
    rw [h7, add_zero] at hxP
    exact ⟨hxP, eq_neg_of_add_eq_zero_left h6⟩

  have hent : ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j := by
    intro x hG i j
    have hx := ((hGood x).mp hG).1
    have h1 := (hSx x hG).1
    apply xClasses_mem I J a hI0 haI hJ
    have hx' : ∀ p q, ∀ α ∈ A, ∃ o : 𝓞 K, (o : K) = (α : K) * (Sx x * Y.map φ) p q := by
      intro p q α hα; rw [← hYK, ← h1]; exact hx p q α hα
    exact xClasses_denom A Y f (Sx x) hx' i j
  set Q := ↥J.toAddSubgroup ⧸ (Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hcardQ : Nat.card Q = Ideal.absNorm I := xClasses_index I J a ha0 hJ
  have : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]; exact fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0))
  let _ : Fintype Q := Fintype.ofFinite Q
  obtain ⟨key, hkey⟩ : ∃ key : Matrix (Fin r) (Fin (r + 1)) K → (Fin r → Fin r → Q),
      ∀ x, Good x → ∀ i j, ∃ o : J.toAddSubgroup,
        ((o : 𝓞 K) : K) = (a : K) * Sx x i j ∧ key x i j = (o : Q) := by
    refine ⟨fun x i j => if h : ∃ o : J.toAddSubgroup, ((o : 𝓞 K) : K) = (a : K) * Sx x i j
      then ((Classical.choose h : J.toAddSubgroup) : Q) else 0, fun x hG i j => ?_⟩
    have h := hent x hG i j
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp only [dif_pos h]⟩
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → Fin r → Q) → Matrix (Fin r) (Fin (r + 1)) K,
      ∀ q, (∃ x, Good x ∧ key x = q) → Good (g q) ∧ key (g q) = q := by
    refine ⟨fun q => if h : ∃ x, Good x ∧ key x = q then Classical.choose h else 0,
      fun q h => ?_⟩
    simp only [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin r → Fin r → Q)).card :=
          Finset.card_image_le
      _ = Fintype.card Q ^ (r ^ 2) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]
      _ = Ideal.absNorm I ^ (r ^ 2) := by rw [← Nat.card_eq_fintype_card, hcardQ]
  · intro x hx hxY
    have hG : Good x := (hGood x).mpr ⟨hx, hxY⟩
    obtain ⟨hG', hk⟩ := hg (key x) ⟨x, hG, rfl⟩
    set x' := g (key x) with hx'
    have hdiff : ∀ i j, ∃ t : 𝓞 K, φ t = Sx x i j - Sx x' i j := by
      intro i j
      obtain ⟨o, ho, hko⟩ := hkey x hG i j
      obtain ⟨o', ho', hko'⟩ := hkey x' hG' i j
      have e : ((o' : J.toAddSubgroup) : Q) = (o : Q) := by
        rw [← hko, ← hko', hk]
      have hm := QuotientAddGroup.eq.mp e
      rw [AddSubgroup.mem_addSubgroupOf] at hm
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨t, ?_⟩
      have ht' : φ t * φ a = φ a * (Sx x i j - Sx x' i j) := by
        rw [← map_mul, ht]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add, map_neg]
        rw [← hc, ← hc, ho, ho']; ring
      exact mul_left_cancel₀ haK (by rw [mul_comm]; exact ht')
    obtain ⟨c, hcc⟩ : ∃ c : Matrix (Fin r) (Fin r) (𝓞 K), ∀ i j, φ (c i j) = Sx x i j - Sx x' i j :=
      ⟨fun i j => Classical.choose (hdiff i j), fun i j => Classical.choose_spec (hdiff i j)⟩
    have hcm : c.map φ = Sx x - Sx x' := by
      ext i j; simp [hcc]
    refine ⟨x', Finset.mem_image_of_mem _ (Finset.mem_univ _), c, ?_, ?_⟩
    · rw [hcm, Matrix.conjTranspose_sub, (hSx x hG).2, (hSx x' hG').2]; abel
    · rw [hcm, Matrix.sub_mul, ← (hSx x hG).1, ← (hSx x' hG').1]; abel
end GlobalTheory
