-- Prove2me | solution 1 for OAI.FiniteCircle.range_distortion_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:47:42.836103+00:00
-- url     : https://prove2.me/submissions/fbb5e0e7-0314-4d50-bba4-a75b5c76c722

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Distortion.lean:L232-L267
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.range_distortion_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Theorems.Thm_OAI_FiniteCircle_weighted_l1_inequality

-- ---- from OAI.Combinatorics.FiniteCircle.Distortion ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem upperRates_finite {α X : Type*} [Finite X] (word : X → List α) (f : X → RealL1) :
    (upperRates word f).Finite := by
  apply (Set.finite_range (fun z : X×X => ‖f z.1-f z.2‖/(editDistance (word z.1) (word z.2):ℝ))).subset
  rintro r ⟨x,y,_,rfl⟩
  exact ⟨(x,y),rfl⟩

 theorem lowerRates_finite {α X : Type*} [Finite X] (word : X → List α) (f : X → RealL1) :
    (lowerRates word f).Finite := by
  apply (Set.finite_range (fun z : X×X => (editDistance (word z.1) (word z.2):ℝ)/‖f z.1-f z.2‖)).subset
  rintro r ⟨x,y,_,rfl⟩
  exact ⟨(x,y),rfl⟩

 theorem finite_l1_embedding (X : Type*) [Fintype X] : ∃ f : X → RealL1, Function.Injective f := by
  classical
  let e : X → ℕ := fun x => (Fintype.equivFin X x).val
  have he : Function.Injective e := fun x y h => (Fintype.equivFin X).injective (Fin.ext h)
  refine ⟨fun x => lp.single 1 (e x) (1:ℝ), ?_⟩
  intro x y h
  by_contra hxy
  have hne : e x ≠ e y := fun h => hxy (he h)
  have ht := congrArg (fun f : RealL1 => f (e x)) h
  simp only [lp.single_apply_self, lp.single_apply, Pi.single_eq_of_ne hne] at ht
  norm_num at ht

 theorem optimalDistortion_lower {α X : Type*} [Fintype X] (word : X → List α) (D : ℝ)
    (hD : ∀ f : X → RealL1, Function.Injective f → D ≤ distortion word f) :
    D ≤ optimalDistortion word := by
  apply le_csInf
  · obtain ⟨f,hf⟩ := finite_l1_embedding X
    exact ⟨distortion word f,f,hf,rfl⟩
  · rintro b ⟨f,hf,rfl⟩
    exact hD f hf

 theorem distortion_control {α X : Type*} [Finite X] [Nontrivial X]
    (word : X → List α) (hw : Function.Injective word)
    (f : X → RealL1) (hf : Function.Injective f) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ distortion word f=A*B ∧
      (∀ x y, ‖f x-f y‖ ≤ A*(editDistance (word x) (word y):ℝ)) ∧
      (∀ x y, (editDistance (word x) (word y):ℝ) ≤ B*‖f x-f y‖) := by
  let A := sSup (upperRates word f)
  let B := sSup (lowerRates word f)
  have hED (x y : X) (hxy : x ≠ y) : (0:ℝ)<editDistance (word x) (word y) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun he => hxy (hw (editDistance_eq_zero.mp he)))
  have hn (x y : X) (hxy : x ≠ y) : 0<‖f x-f y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hxy (hf he)))
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have ha : ‖f x-f y‖/(editDistance (word x) (word y):ℝ) ≤ A :=
    le_csSup (upperRates_finite word f).bddAbove ⟨x,y,hxy,rfl⟩
  have hb : (editDistance (word x) (word y):ℝ)/‖f x-f y‖ ≤ B :=
    le_csSup (lowerRates_finite word f).bddAbove ⟨x,y,hxy,rfl⟩
  refine ⟨A,B,(div_pos (hn x y hxy) (hED x y hxy)).trans_le ha,
    (div_pos (hED x y hxy) (hn x y hxy)).trans_le hb,rfl,?_,?_⟩
  · intro x y
    by_cases hxy : x=y
    · subst y; simp
    · exact (div_le_iff₀ (hED x y hxy)).mp (le_csSup (upperRates_finite word f).bddAbove ⟨x,y,hxy,rfl⟩)
  · intro x y
    by_cases hxy : x=y
    · subst y; simp
    · exact (div_le_iff₀ (hn x y hxy)).mp (le_csSup (lowerRates_finite word f).bddAbove ⟨x,y,hxy,rfl⟩)

 theorem dyadic_expected_budget {I : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (f : (I → ZMod M) → RealL1)
    (A u L copies : ℝ) (hcL : L=(M:ℝ)*Fintype.card I*copies)
    (hrsingle : ∀ (i : I) (j : Fin (Nat.log 2 M+1)),
      (𝔼 v, ‖f (v+Pi.single i ((2^j.val:ℕ):ZMod M))-f v‖) ≤ A*(u*2*copies*(2:ℝ)^j.val))
    : (∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
      (𝔼 v, ‖f (v+Pi.single i ((2^j.val:ℕ):ZMod M))-f v‖)) ≤
      A*u*2*L*(Nat.log 2 M+1:ℕ) := by
  classical
  calc
      _ ≤ ∑ i : I, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val*(A*(u*2*copies*(2:ℝ)^j.val)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hrsingle i j) (by positivity)
      _ = ∑ _i : I, ∑ _j : Fin (Nat.log 2 M+1), (M:ℝ)*A*u*2*copies := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        field_simp
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [hcL]; ring

 theorem fourier_edit_distortion {I α : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0<B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ w≠1 →
      B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (h R L copies u δ : ℝ) (hL : 0<L)
    (hcL : L=(M:ℝ)*Fintype.card I*copies)
    (hcheap : ∀ v (c : H), (editDistance (W v) (W (v+c)):ℝ) ≤ u*2*h*L/R)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      (editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))):ℝ) ≤ u*2*copies*(2:ℝ)^j.val)
    (hlong : ∀ v, δ*L ≤ (editDistance (W v) (W (v+w)):ℝ))
    (f : (I → ZMod M) → RealL1) (A A' : ℝ) (hA : 0≤A) (hA' : 0≤A')
    (hu : ∀ v z, ‖f (v+z)-f v‖ ≤ A*(editDistance (W v) (W (v+z)):ℝ))
    (hl : ∀ v z, (editDistance (W v) (W (v+z)):ℝ) ≤ A'*‖f (v+z)-f v‖) :
    δ ≤ (A*A')*u*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B) := by
  classical
  have hleft : δ*L ≤ A'*(𝔼 v, ‖f (v+w)-f v‖) := by
    rw [Finset.mul_expect]
    apply Finset.le_expect Finset.univ_nonempty
    intro v _
    exact (hlong v).trans (hl v w)
  have hrcheap : (𝔼 c : H, 𝔼 v, ‖f (v+c)-f v‖) ≤ A*(u*2*h*L/R) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro c _
    apply Finset.expect_le Finset.univ_nonempty
    intro v _
    exact (hu v c).trans (mul_le_mul_of_nonneg_left (hcheap v c) hA)
  have hrsingle (i : I) (j : Fin (Nat.log 2 M+1)) :
      (𝔼 v, ‖f (v+Pi.single i ((2^j.val:ℕ):ZMod M))-f v‖) ≤ A*(u*2*copies*(2:ℝ)^j.val) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro v _
    exact (hu v _).trans (mul_le_mul_of_nonneg_left (hsingle v i j) hA)
  have hsum := dyadic_expected_budget f A u L copies hcL hrsingle
  have hspec := weighted_l1_inequality H w B hB hb f
  have hbd := add_le_add (mul_le_mul_of_nonneg_left hrcheap (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hB)))
  have hright := hspec.trans hbd
  have heq : 2*(A*(u*2*h*L/R))+(1/B)*(A*u*2*L*(Nat.log 2 M+1:ℕ)) =
      A*u*L*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B) := by ring
  rw [heq] at hright
  have ht := hleft.trans (mul_le_mul_of_nonneg_left hright hA')
  have he : A'*(A*u*L*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B)) =
      ((A*A')*u*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B))*L := by ring
  rw [he] at ht
  exact le_of_mul_le_mul_right ht hL

 theorem range_distortion_lower {I α : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0<B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ w≠1 →
      B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (h R L copies u δ D : ℝ) (hL : 0<L) (hδ : 0<δ)
    (hcL : L=(M:ℝ)*Fintype.card I*copies)
    (hcheap : ∀ v (c : H), (editDistance (W v) (W (v+c)):ℝ) ≤ u*2*h*L/R)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      (editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))):ℝ) ≤ u*2*copies*(2:ℝ)^j.val)
    (hlong : ∀ v, δ*L ≤ (editDistance (W v) (W (v+w)):ℝ))
    (hnum : ∀ t : ℝ, 0≤t → δ ≤ t*u*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B) → D≤t) :
    D ≤ optimalDistortion (fun x : Set.range W => x.val) := by
  classical
  let X := Set.range W
  let : Fintype X := (Set.finite_range W).fintype
  have hw0 : W 0 ≠ W w := by
    intro he
    have ht := hlong 0
    simp only [zero_add, ← he,editDistance_self,Nat.cast_zero] at ht
    exact (mul_pos hδ hL).not_ge ht
  let : Nontrivial X := ⟨⟨⟨W 0,⟨0,rfl⟩⟩,⟨W w,⟨w,rfl⟩⟩,fun he => hw0 (congrArg Subtype.val he)⟩⟩
  apply optimalDistortion_lower
  intro f hf
  obtain ⟨A,A',hA,hA',hD,hu,hl⟩ := distortion_control (fun x : X => x.val) Subtype.val_injective f hf
  let F := fun v => f (⟨W v,⟨v,rfl⟩⟩ : X)
  have hcontrolu (v z : I → ZMod M) : ‖F (v+z)-F v‖ ≤ A*(editDistance (W v) (W (v+z)):ℝ) := by
    rw [norm_sub_rev]
    exact hu ⟨W v,⟨v,rfl⟩⟩ ⟨W (v+z),⟨v+z,rfl⟩⟩
  have hcontroll (v z : I → ZMod M) : (editDistance (W v) (W (v+z)):ℝ) ≤ A'*‖F (v+z)-F v‖ := by
    rw [norm_sub_rev]
    exact hl ⟨W v,⟨v,rfl⟩⟩ ⟨W (v+z),⟨v+z,rfl⟩⟩
  have ht := fourier_edit_distortion H w B hB hb W h R L copies u δ hL hcL hcheap hsingle hlong
    F A A' hA.le hA'.le hcontrolu hcontroll
  rw [hD]
  exact hnum (A*A') (mul_nonneg hA.le hA'.le) ht

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.range_distortion_lower := @_root_.OAI.FiniteCircle.range_distortion_lower
