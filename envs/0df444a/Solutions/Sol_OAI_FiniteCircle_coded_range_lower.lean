-- Prove2me | solution 1 for OAI.FiniteCircle.coded_range_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:58:49.290046+00:00
-- url     : https://prove2.me/submissions/43c89dc2-705f-42d8-a0f2-323c6de7de0e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BinaryDistortion.lean:L11-L57
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.coded_range_lower. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_lower_numeric
import Theorems.Thm_OAI_FiniteCircle_range_distortion_lower

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

end EditScript

theorem sublist_common_large {α : Type*} {x y z : List α} (hx : x <+ z) (hy : y <+ z) :
    ∃ u : List α, u <+ x ∧ u <+ y ∧ x.length + y.length ≤ u.length + z.length := by
  induction z generalizing x y with
  | nil =>
    have : x = [] := List.sublist_nil.mp hx
    have : y = [] := List.sublist_nil.mp hy
    subst x; subst y
    exact ⟨[], .slnil, .slnil, le_rfl⟩
  | cons a z ih =>
    cases hx with
    | cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy.cons a, by simp only [List.length_cons]; omega⟩
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux.cons a, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨a :: u, hux.cons_cons a, huy.cons_cons a, by simp only [List.length_cons]; omega⟩

theorem lcs_triangle {α : Type*} (x y z : List α) : lcs x y + lcs y z ≤ y.length + lcs x z := by
  obtain ⟨a, hax, hay, ha⟩ := lcs_exists x y
  obtain ⟨b, hby, hbz, hb⟩ := lcs_exists y z
  obtain ⟨u, hua, hub, hlen⟩ := sublist_common_large hay hby
  have hle := le_lcs (hua.trans hax) (hub.trans hbz)
  omega

theorem unequalDeficit_triangle {α : Type*} (x y z : List α) :
    unequalDeficit x z ≤ unequalDeficit x y + unequalDeficit y z := by
  have hxy := lcs_le_length_left x y
  have hyx := lcs_le_length_right x y
  have hyz := lcs_le_length_left y z
  have hzy := lcs_le_length_right y z
  have hxz := lcs_le_length_left x z
  have hzx := lcs_le_length_right x z
  have ht := lcs_triangle x y z
  simp only [unequalDeficit]
  omega

theorem EditStep.unequalDeficit_le {α : Type*} {x y : List α} (h : EditStep x y) :
    unequalDeficit x y ≤ 1 := by
  cases h with
  | insert u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs (List.Sublist.refl (u ++ v)) hs
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | delete u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs hs (List.Sublist.refl (u ++ v))
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | substitute u v a b =>
    have ha : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hb : u ++ v <+ u ++ b :: v := (List.Sublist.refl v).cons b |>.append_left u
    have hl := le_lcs ha hb
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega

theorem EditScript.unequalDeficit_le {α : Type*} {n : ℕ} {x y : List α} (h : EditScript n x y) :
    unequalDeficit x y ≤ n := by
  induction h with
  | nil => simp
  | cons h hs ih =>
    exact (unequalDeficit_triangle _ _ _).trans ((Nat.add_le_add h.unequalDeficit_le ih).trans_eq (Nat.add_comm _ _))

theorem unequalDeficit_le_editDistance {α : Type*} (x y : List α) :
    unequalDeficit x y ≤ editDistance x y := (editDistance_spec x y).unequalDeficit_le

theorem deficit_eq_unequalDeficit {α : Type*} {x y : List α} (h : x.length = y.length) :
    deficit x y = unequalDeficit x y := by simp [deficit, unequalDeficit, h]

theorem deficit_le_editDistance {α : Type*} {x y : List α} (h : x.length = y.length) :
    deficit x y ≤ editDistance x y := by
  rw [deficit_eq_unequalDeficit h]
  exact unequalDeficit_le_editDistance x y

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.BinaryDistortion ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem coded_range_lower {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    {n k M : ℕ} [NeZero M] (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13)
    (H : AddSubgroup (I → ZMod M)) [Fintype H] (θ : I → ZMod M)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ θ≠1 →
      (((n^4:ℕ):ℝ)/2)^(n^4) ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (L copies : ℕ) (hL : 0<L)
    (hcL : L=M*Fintype.card I*copies) (hLen : ∀ v, (W v).length=L)
    (hcheap : ∀ v (c : H), (n^4)^(2*n^4)*editDistance (W v) (W (v+c)) ≤ 2*n^4*L)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))) ≤ 2*copies*2^j.val)
    (hlong : ∀ v, (L:ℝ)/(n:ℝ)^(3*n^4) ≤ (deficit (W v) (W (v+θ)):ℝ))
    {w : ℕ} (c : α → Fin w → Bool) (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ optimalDistortion (fun x : Set.range (fun v => encode c (W v)) => x.val) := by
  classical
  have hn0 : 0<n := by omega
  have hR : (0:ℝ)<((n^4)^(2*n^4):ℕ) := by positivity
  apply range_distortion_lower H θ ((((n^4:ℕ):ℝ)/2)^(n^4)) (by positivity) hb
    (fun v => encode c (W v)) (n^4) ((n^4)^(2*n^4):ℕ) L copies w
    ((1/268435456)*w/(n:ℝ)^(3*n^4)) ((n:ℝ)^k) (by positivity) (by have := hc.1; positivity)
    (by exact_mod_cast hcL)
  · intro v z
    apply (le_div_iff₀ hR).mpr
    have he := hc.2.2.2 (W v) (W (v+z))
    have ht := Nat.mul_le_mul_left ((n^4)^(2*n^4)) he
    have hh := Nat.mul_le_mul_left w (hcheap v z)
    have hn : editDistance (encode c (W v)) (encode c (W (v+z)))*((n^4)^(2*n^4)) ≤ w*2*n^4*L := by
      nlinarith
    exact_mod_cast hn
  · intro v i j
    have he := (hc.2.2.2 (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M)))).trans
      (Nat.mul_le_mul_left w (hsingle v i j))
    have hn : editDistance (encode c (W v)) (encode c (W (v+Pi.single i ((2^j.val:ℕ):ZMod M)))) ≤
        w*2*copies*2^j.val := by nlinarith
    exact_mod_cast hn
  · intro v
    have hd := (hc.2.2.1 L (W v) (W (v+θ)) (hLen v) (hLen (v+θ))).1
    have he := deficit_le_editDistance (x:=encode c (W v)) (y:=encode c (W (v+θ))) (by simp only [length_encode,hLen])
    calc
      _ = (1/268435456)*w*((L:ℝ)/(n:ℝ)^(3*n^4)) := by ring
      _ ≤ (1/268435456)*w*(deficit (W v) (W (v+θ)):ℝ) :=
        mul_le_mul_of_nonneg_left (hlong v) (by positivity)
      _ ≤ (deficit (encode c (W v)) (encode c (W (v+θ))):ℝ) := hd
      _ ≤ _ := by exact_mod_cast he
  · intro t _ ht
    apply lower_numeric hn hk hJ hc.1 t
    simpa only [Nat.cast_pow] using ht

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.coded_range_lower := @_root_.OAI.FiniteCircle.coded_range_lower
