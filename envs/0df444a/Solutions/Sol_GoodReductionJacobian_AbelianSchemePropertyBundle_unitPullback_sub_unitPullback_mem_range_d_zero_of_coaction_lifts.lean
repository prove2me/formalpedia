-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b9df7c04-8db2-5d70-abf5-e9339cbb0afb

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace T1dAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

section Sheaf

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) {m : ℕ} (z : (OModulePresheaf.unit πY).cochain 𝒦 m)

noncomputable def pb (T : 𝒦.Idx m) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) : Γ(X, W) :=
  (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter T)).hom (z T))

theorem map_pb (T : 𝒦.Idx m) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ 𝒦.inter T) :
    (X.presheaf.map (homOfLE hW').op).hom (pb h 𝒦 z T W hW) = pb h 𝒦 z T W' hW'' := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem pb_congr {T T' : 𝒦.Idx m} (e : T = T') (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter T) (hW' : W ≤ h ⁻¹ᵁ 𝒦.inter T') :
    pb h 𝒦 z T W hW = pb h 𝒦 z T' W hW' := by
  subst e; rfl

theorem map_app_map_eq_pb (S : 𝒦.Idx (m + 1)) (i : Fin (m + 2)) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ 𝒦.inter S) :
    (X.presheaf.map (homOfLE hW).op).hom ((h.app (𝒦.inter S)).hom
      ((Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face S i)).op).hom (z (𝒦.face S i)))) =
      pb h 𝒦 z (𝒦.face S i) W (hW.trans (h.preimage_mono (𝒦.inter_le_inter_face S i))) := by
  unfold pb
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality_assoc, ← X.presheaf.map_comp,
    ← CommRingCat.comp_apply]
  rfl

end Sheaf

section Pairs

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒦 : Y.OrderedAffineCover) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)

def pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exact hij)⟩

theorem pair_val {i j : 𝒦.ι} (hij : i < j) : (pair 𝒦 hij).1 = ![i, j] := rfl

theorem inf_le_inter_pair {i j : 𝒦.ι} (hij : i < j) : 𝒦.U i ⊓ 𝒦.U j ≤ 𝒦.inter (pair 𝒦 hij) :=
  le_iInf fun k => by fin_cases k; exacts [inf_le_left, inf_le_right]

def triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.Idx 2 :=
  ⟨![a, b, c], Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k; exacts [hab, hbc])⟩

theorem inf_le_inter_triple {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c ≤ 𝒦.inter (triple 𝒦 hab hbc) :=
  le_iInf fun k => by
    fin_cases k
    exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]

theorem face_triple_zero {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 0 = pair 𝒦 hbc := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_one {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 1 = pair 𝒦 (hab.trans hbc) := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face_triple_two {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c) : 𝒦.face (triple 𝒦 hab hbc) 2 = pair 𝒦 hab := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

noncomputable def P {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) :=
  pb h 𝒦 z (pair 𝒦 hij) W (hW.trans (h.preimage_mono (inf_le_inter_pair 𝒦 hij)))

theorem map_P {i j : 𝒦.ι} (hij : i < j) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W)
    (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (P h 𝒦 z hij W hW) = P h 𝒦 z hij W' hW'' :=
  map_pb h 𝒦 z _ _ hW' _

theorem P_add_P (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) {a b c : 𝒦.ι} (hab : a < b) (hbc : b < c)
    (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c)) :
    P h 𝒦 z hab W (hW.trans (h.preimage_mono inf_le_left)) + P h 𝒦 z hbc W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      P h 𝒦 z (hab.trans hbc) W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by
  have hle : W ≤ h ⁻¹ᵁ 𝒦.inter (triple 𝒦 hab hbc) := hW.trans (h.preimage_mono (inf_le_inter_triple 𝒦 hab hbc))
  have hd := congrFun hz (triple 𝒦 hab hbc)
  rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_three] at hd
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_zsmul, neg_one_zsmul] at hd
  change (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 0)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 0)) +
        -(Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 1)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 1)) +
        (Y.presheaf.map (homOfLE (𝒦.inter_le_inter_face _ 2)).op).hom (z (𝒦.face (triple 𝒦 hab hbc) 2))
      = (0 : Γ(Y, 𝒦.inter (triple 𝒦 hab hbc))) at hd
  have hd' := congrArg (fun y => (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter (triple 𝒦 hab hbc))).hom y)) hd
  simp only [map_add, map_neg, map_zero] at hd'
  rw [map_app_map_eq_pb, map_app_map_eq_pb, map_app_map_eq_pb,
    pb_congr h 𝒦 z (face_triple_zero 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hbc))),
    pb_congr h 𝒦 z (face_triple_one 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 (hab.trans hbc)))),
    pb_congr h 𝒦 z (face_triple_two 𝒦 hab hbc) W _ ((hW.trans (h.preimage_mono inf_le_left)).trans
      (h.preimage_mono (inf_le_inter_pair 𝒦 hab)))] at hd'
  unfold P
  linear_combination hd'

noncomputable def Z (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Γ(X, W) := by
  classical
  exact if hij : i < j then P h 𝒦 z hij W hW
    else if hji : j < i then -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _))))
    else 0

theorem Z_of_lt {i j : 𝒦.ι} (hij : i < j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = P h 𝒦 z hij W hW := by
  classical
  simp only [Z, dif_pos hij]

theorem Z_of_gt {i j : 𝒦.ι} (hji : j < i) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    Z h 𝒦 z i j W hW = -P h 𝒦 z hji W (hW.trans (h.preimage_mono (le_of_eq (inf_comm _ _)))) := by
  classical
  simp only [Z, dif_neg (not_lt_of_gt hji), dif_pos hji]

theorem Z_self (i : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U i)) : Z h 𝒦 z i i W hW = 0 := by
  classical
  simp only [Z, dif_neg (lt_irrefl i)]

theorem Z_of_eq {i j : 𝒦.ι} (e : i = j) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) : Z h 𝒦 z i j W hW = 0 := by
  subst e; exact Z_self h 𝒦 z i W hW

theorem map_Z (i j : 𝒦.ι) {W W' : X.Opens} (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W' ≤ W) (hW'' : W' ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) :
    (X.presheaf.map (homOfLE hW').op).hom (Z h 𝒦 z i j W hW) = Z h 𝒦 z i j W' hW'' := by
  classical
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_lt h 𝒦 z hij, map_P]
  · simp only [Z_self, map_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_gt h 𝒦 z hji, map_neg, map_P]

theorem Z_swap (i j : 𝒦.ι) (W : X.Opens) (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j)) (hW' : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i)) :
    Z h 𝒦 z j i W hW' = -Z h 𝒦 z i j W hW := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [Z_of_lt h 𝒦 z hij, Z_of_gt h 𝒦 z hij]
  · simp only [Z_self, neg_zero]
  · rw [Z_of_gt h 𝒦 z hji, Z_of_lt h 𝒦 z hji, neg_neg]

theorem Z_add_Z (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) (i j l : 𝒦.ι) (W : X.Opens)
    (hW : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l)) :
    Z h 𝒦 z i j W (hW.trans (h.preimage_mono inf_le_left)) +
        Z h 𝒦 z j l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))) =
      Z h 𝒦 z i l W (hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))) := by

  have key : ∀ (a b c : 𝒦.ι) (hab : a < b) (hbc : b < c) (V : X.Opens) (hV : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c))
      (h₁ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b)) (h₂ : V ≤ h ⁻¹ᵁ (𝒦.U b ⊓ 𝒦.U c)) (h₃ : V ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U c)),
      Z h 𝒦 z a b V h₁ + Z h 𝒦 z b c V h₂ = Z h 𝒦 z a c V h₃ := by
    intro a b c hab hbc V hV h₁ h₂ h₃
    rw [Z_of_lt h 𝒦 z hab, Z_of_lt h 𝒦 z hbc, Z_of_lt h 𝒦 z (hab.trans hbc)]
    exact P_add_P h 𝒦 z hz hab hbc V hV
  have hWij : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j) := hW.trans (h.preimage_mono inf_le_left)
  have hWjl : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_right))
  have hWil : W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U l) := hW.trans (h.preimage_mono (inf_le_inf_right _ inf_le_left))
  have hWji : W ≤ h ⁻¹ᵁ (𝒦.U j ⊓ 𝒦.U i) := hWij.trans (le_of_eq (by rw [inf_comm]))
  have hWlj : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U j) := hWjl.trans (le_of_eq (by rw [inf_comm]))
  have hWli : W ≤ h ⁻¹ᵁ (𝒦.U l ⊓ 𝒦.U i) := hWil.trans (le_of_eq (by rw [inf_comm]))
  have perm : ∀ (a b c : 𝒦.ι), W ≤ h ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l) →
      ({a, b, c} : Set 𝒦.ι) ⊆ {i, j, l} → W ≤ h ⁻¹ᵁ (𝒦.U a ⊓ 𝒦.U b ⊓ 𝒦.U c) := by
    intro a b c hW habc
    refine hW.trans (h.preimage_mono ?_)
    have mem : ∀ x ∈ ({i, j, l} : Set 𝒦.ι), 𝒦.U i ⊓ 𝒦.U j ⊓ 𝒦.U l ≤ 𝒦.U x := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      exacts [inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right]
    exact le_inf (le_inf (mem a (habc (by simp))) (mem b (habc (by simp)))) (mem c (habc (by simp)))
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · exact key i j l hij hjl W hW hWij hWjl hWil
    · rw [Z_self, add_zero]
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key i l j hil hlj W (perm i l j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWil hWlj hWij
        rw [Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key l i j hli hij W (perm l i j hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWli hWij hWlj
        rw [Z_swap h 𝒦 z i l W hWil hWli, Z_swap h 𝒦 z j l W hWjl hWlj] at e
        linear_combination e
  · rw [Z_self, zero_add]
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        have e := key j i l hji hil W (perm j i l hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWji hWil hWjl
        rw [Z_swap h 𝒦 z i j W hWij hWji] at e
        linear_combination -e
      ·
        rw [Z_self, Z_swap h 𝒦 z i j W hWij hWji, add_neg_cancel]
      ·
        have e := key j l i hjl hli W (perm j l i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWjl hWli hWji
        rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z i l W hWil hWli] at e
        linear_combination e
    · rw [Z_self, add_zero]
    ·
      have e := key l j i hlj hji W (perm l j i hW (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hWlj hWji hWli
      rw [Z_swap h 𝒦 z i j W hWij hWji, Z_swap h 𝒦 z j l W hWjl hWlj, Z_swap h 𝒦 z i l W hWil hWli] at e
      linear_combination -e

end Pairs

section Branches

variable {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R')) {πY : Y ⟶ Spec (.of R)}
  (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

theorem inter_le_two (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (s : 𝒲.Idx 1) : 𝒲.inter s ≤ h ⁻¹ᵁ (𝒦.U (lam (s.1 0)) ⊓ 𝒦.U (lam (s.1 1))) := by
  rw [Scheme.Hom.preimage_inf]
  exact le_inf ((𝒲.inter_le s 0).trans (hlam _)) ((𝒲.inter_le s 1).trans (hlam _))

theorem unitPullback_one_eq_Z (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (z : (OModulePresheaf.unit πY).cochain 𝒦 1)
    (s : 𝒲.Idx 1) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z s =
      Z h 𝒦 z (lam (s.1 0)) (lam (s.1 1)) (𝒲.inter s) (inter_le_two h 𝒲 𝒦 lam hlam s) := by
  classical
  have hs01 : s.1 0 < s.1 1 := s.2 (by decide)
  rcases lt_trichotomy (lam (s.1 0)) (lam (s.1 1)) with hlt | heq | hgt
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_lt hlt)
      · exact absurd hab (ne_of_gt hlt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.refl _ := by
      rw [Tuple.sort_eq_refl_iff_monotone]
      intro a b hab
      fin_cases a <;> fin_cases b
      · exact le_rfl
      · exact le_of_lt hlt
      · exact absurd hab (by decide)
      · exact le_rfl
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hlt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort, Equiv.Perm.sign_refl,
      Units.val_one, one_smul, Z_of_lt h 𝒦 z hlt]
    exact pb_congr h 𝒦 z hidx _ _ _
  ·
    have hninj : ¬ Function.Injective (lam ∘ s.1) := fun hinj => absurd (hinj (a₁ := 0) (a₂ := 1) heq) (by decide)
    rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hninj]
    exact (Z_of_eq h 𝒦 z heq _ _).symm
  ·
    have hinj : Function.Injective (lam ∘ s.1) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_gt hgt)
      · exact absurd hab (ne_of_lt hgt)
      · rfl
    have hsort : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := by
      symm
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · intro a b hab
        fin_cases a <;> fin_cases b
        · exact le_rfl
        · exact le_of_lt (by simpa using hgt)
        · exact absurd hab (by decide)
        · exact le_rfl
      · intro a b hab hfab
        exact absurd ((Equiv.swap (0 : Fin 2) 1).injective (hinj hfab)) (ne_of_lt hab)
    have hidx : 𝒲.sortIdx 𝒦 lam s hinj = pair 𝒦 hgt := by
      apply Subtype.ext
      rw [Scheme.OrderedAffineCover.sortIdx_val, hsort, pair_val]
      funext k; fin_cases k <;> rfl
    rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam 1 z s hinj, hsort,
      Equiv.Perm.sign_swap (by decide), Units.val_neg, Units.val_one, neg_one_smul, Z_of_gt h 𝒦 z hgt]
    congr 1
    exact pb_congr h 𝒦 z hidx _ _ _

end Branches

end T1dAux

namespace T1dAux2
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

theorem isAffineOpen_inter (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) {n : ℕ} (t : 𝒦.Idx n) :
    IsAffineOpen (𝒦.inter t) := by
  haveI : IsSeparated f := hA.proper.toIsSeparated
  haveI : IsSeparated (terminal.from A) := by rw [← terminal.comp_from f]; infer_instance
  haveI : IsAffineHom (pullback.diagonal (terminal.from A)) := inferInstance
  exact IsAffineOpen.iInf (fun j => 𝒦.isAffineOpen (t.1 j))

end T1dAux2

open T1dAux T1dAux2 in
theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∀ (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
      (hnat : ∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
          (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
            ρ U' ((A.presheaf.map (homOfLE hle).op).hom s))
      (hinj : ∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom)
      (hcoinv : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom)

      (φ : A ⟶ A) (hφN : φ ≫ N = N ≫ φ) (φH : H →ₐ[K] H)
      (hequiv : ∀ (U W : A.affineOpens) (hle : N ⁻¹ᵁ (W : A.Opens) ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
        ∃ Ξ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →+* Γ(A, N ⁻¹ᵁ (W : A.Opens)) ⊗[K] H,
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (s ⊗ₜ[K] (1 : H)) = (φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s ⊗ₜ[K] (1 : H)) ∧
          (∀ x : H, Ξ ((1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] x) = (1 : Γ(A, N ⁻¹ᵁ (W : A.Opens))) ⊗ₜ[K] φH x) ∧
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (ρ U s) = ρ W ((φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s)))

      (𝒦 𝒲 : A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
      (hlam : ∀ w, 𝒲.U w ≤ φ ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' w))

      (h h' : H) (hh' : φH h = h')
      (S S' : ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ 𝒦.U i))
      (hS : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S i) = S i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h)
      (hS' : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S' i) = S' i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h')
      (c c' : (OModulePresheaf.unit f).cochain 𝒦 1)
      (hc : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S (t.1 1)))
      (hc' : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c' t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S' (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S' (t.1 1))),
    OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1 c -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1 c' ∈
      LinearMap.range ((OModulePresheaf.unit f).d 𝒲 0) := by
  intro ρ hnat hinj hcoinv φ hφN φH hequiv 𝒦 𝒲 lam lam' hlam hlam' h h' hh' S S' hS hS' c c' hc hc'
  classical
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V

  let Wa : 𝒲.ι → A.affineOpens := fun w => ⟨𝒲.U w, 𝒲.isAffineOpen w⟩
  let Ka : 𝒦.ι → A.affineOpens := fun i => ⟨𝒦.U i, 𝒦.isAffineOpen i⟩

  have appLE_congr_hom : ∀ (g₁ g₂ : A ⟶ A) (_ : g₁ = g₂) (U V : A.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U),
      g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
    rintro g₁ g₂ rfl U V e₁ e₂; rfl
  have id_appLE : ∀ (U V : A.Opens) (e : V ≤ (𝟙 A) ⁻¹ᵁ U),
      Scheme.Hom.appLE (𝟙 A) U V e = A.presheaf.map (homOfLE e).op := by
    intro U V e
    show (𝟙 A : A ⟶ A).app U ≫ A.presheaf.map (homOfLE e).op = _
    rw [Scheme.Hom.id_app]
    exact Category.id_comp _

  have hcomm : ∀ V : A.Opens, φ ⁻¹ᵁ (N ⁻¹ᵁ V) = N ⁻¹ᵁ (φ ⁻¹ᵁ V) := by
    intro V
    have h1 := congrArg (fun g : A ⟶ A => g ⁻¹ᵁ V) hφN
    simpa only [Scheme.Hom.comp_preimage] using h1
  have hpre : ∀ w, N ⁻¹ᵁ 𝒲.U w ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.U (lam w)) := fun w => by
    rw [hcomm]; exact N.preimage_mono (hlam w)
  have hpre' : ∀ w, N ⁻¹ᵁ 𝒲.U w ≤ N ⁻¹ᵁ 𝒦.U (lam' w) := fun w => N.preimage_mono (hlam' w)

  let R : ∀ w, Γ(A, N ⁻¹ᵁ 𝒲.U w) := fun w =>
    (φ.appLE (N ⁻¹ᵁ 𝒦.U (lam w)) (N ⁻¹ᵁ 𝒲.U w) (hpre w)).hom (S (lam w))
  let R' : ∀ w, Γ(A, N ⁻¹ᵁ 𝒲.U w) := fun w =>
    (A.presheaf.map (homOfLE (hpre' w)).op).hom (S' (lam' w))
  have hR : ∀ w, ρ (Wa w) (R w) = R w ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒲.U w)) ⊗ₜ[K] h' := by
    intro w
    obtain ⟨Ξ, hΞ1, hΞ2, hΞ3⟩ := hequiv (Ka (lam w)) (Wa w) (hpre w)
    have e3 := hΞ3 (S (lam w))
    rw [hS (lam w), map_add, hΞ1, hΞ2, hh'] at e3
    exact e3.symm
  have hR' : ∀ w, ρ (Wa w) (R' w) = R' w ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒲.U w)) ⊗ₜ[K] h' := by
    intro w
    have hn := hnat (Ka (lam' w)) (Wa w) (hpre' w) (S' (lam' w))
    rw [hS' (lam' w), map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at hn
    simp only [map_one, AlgHom.id_apply] at hn
    exact hn.symm
  have hdiff : ∀ w, ρ (Wa w) (R w - R' w) = (R w - R' w) ⊗ₜ[K] (1 : H) := by
    intro w
    rw [map_sub, hR, hR', TensorProduct.sub_tmul]
    abel
  have hbt : ∀ w, ∃ b : Γ(A, 𝒲.U w), (N.app (𝒲.U w)).hom b = R w - R' w := fun w =>
    hcoinv (Wa w) _ (hdiff w)
  choose bt hbt using hbt
  let b : (OModulePresheaf.unit f).cochain 𝒲 0 := fun s => (OModulePresheaf.unit f).res (𝒲.inter_le s 0) (bt (s.1 0))
  have hΦeq : ∀ (i i' : 𝒦.ι) (_ : i = i') (W : A.Opens) (e₁ : W ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.U i)) (e₂ : W ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.U i')),
      (φ.appLE (N ⁻¹ᵁ 𝒦.U i) W e₁).hom (S i) = (φ.appLE (N ⁻¹ᵁ 𝒦.U i') W e₂).hom (S i') := by
    rintro i i' rfl W e₁ e₂; rfl
  have hΦ'eq : ∀ (i i' : 𝒦.ι) (_ : i = i') (W : A.Opens) (e₁ : W ≤ N ⁻¹ᵁ 𝒦.U i) (e₂ : W ≤ N ⁻¹ᵁ 𝒦.U i'),
      (A.presheaf.map (homOfLE e₁).op).hom (S' i) = (A.presheaf.map (homOfLE e₂).op).hom (S' i') := by
    rintro i i' rfl W e₁ e₂; rfl

  have hNP : ∀ {i j : 𝒦.ι} (hij : i < j) (W : A.Opens) (hW : W ≤ φ ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j))
      (ei : N ⁻¹ᵁ W ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.U i)) (ej : N ⁻¹ᵁ W ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.U j)),
      (N.app W).hom (P φ 𝒦 c hij W hW) =
        (φ.appLE (N ⁻¹ᵁ 𝒦.U i) (N ⁻¹ᵁ W) ei).hom (S i) - (φ.appLE (N ⁻¹ᵁ 𝒦.U j) (N ⁻¹ᵁ W) ej).hom (S j) := by
    intro i j hij W hW ei ej
    have hW' : W ≤ φ ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij) := hW.trans (φ.preimage_mono (inf_le_inter_pair 𝒦 hij))
    have eV : N ⁻¹ᵁ W ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) := by
      rw [hcomm]; exact N.preimage_mono hW'
    have e1 : P φ 𝒦 c hij W hW = (φ.appLE (𝒦.inter (pair 𝒦 hij)) W hW').hom (c (pair 𝒦 hij)) := rfl
    have chain : φ.appLE (𝒦.inter (pair 𝒦 hij)) W hW' ≫ N.appLE W (N ⁻¹ᵁ W) le_rfl =
        N.appLE (𝒦.inter (pair 𝒦 hij)) (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) le_rfl ≫
          φ.appLE (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) (N ⁻¹ᵁ W) eV := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr_hom _ _ hφN.symm _ _ _ _
    have e2 : (N.app W).hom ((φ.appLE (𝒦.inter (pair 𝒦 hij)) W hW').hom (c (pair 𝒦 hij))) =
        (φ.appLE (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) (N ⁻¹ᵁ W) eV).hom
          ((N.app (𝒦.inter (pair 𝒦 hij))).hom (c (pair 𝒦 hij))) := by
      have := congrArg (fun g => g.hom (c (pair 𝒦 hij))) chain
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [Scheme.Hom.app_eq_appLE N, Scheme.Hom.app_eq_appLE N]
      exact this
    rw [e1, e2, hc (pair 𝒦 hij), map_sub]
    congr 1
    · show ((A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le (pair 𝒦 hij) 0))).op ≫
          φ.appLE (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) (N ⁻¹ᵁ W) eV)).hom (S i) = _
      rw [Scheme.Hom.map_appLE]
      exact hΦeq _ _ rfl _ _ _
    · show ((A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le (pair 𝒦 hij) 1))).op ≫
          φ.appLE (N ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij)) (N ⁻¹ᵁ W) eV)).hom (S j) = _
      rw [Scheme.Hom.map_appLE]
      exact hΦeq _ _ rfl _ _ _

  have hNat : ∀ (V W : A.Opens) (e : W ≤ V) (x : Γ(A, V)),
      (N.app W).hom ((A.presheaf.map (homOfLE e).op).hom x) =
        (A.presheaf.map (homOfLE (N.preimage_mono e)).op).hom ((N.app V).hom x) := by
    intro V W e x
    show (A.presheaf.map (homOfLE e).op ≫ N.app W).hom x = (N.app V ≫ A.presheaf.map (homOfLE (N.preimage_mono e)).op).hom x
    rw [Scheme.Hom.app_eq_appLE N, Scheme.Hom.app_eq_appLE N, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

  have hNP' : ∀ {i j : 𝒦.ι} (hij : i < j) (W : A.Opens) (hW : W ≤ (𝟙 A) ⁻¹ᵁ (𝒦.U i ⊓ 𝒦.U j))
      (ei : N ⁻¹ᵁ W ≤ N ⁻¹ᵁ 𝒦.U i) (ej : N ⁻¹ᵁ W ≤ N ⁻¹ᵁ 𝒦.U j),
      (N.app W).hom (P (𝟙 A) 𝒦 c' hij W hW) =
        (A.presheaf.map (homOfLE ei).op).hom (S' i) - (A.presheaf.map (homOfLE ej).op).hom (S' j) := by
    intro i j hij W hW ei ej
    have hW' : W ≤ (𝟙 A) ⁻¹ᵁ 𝒦.inter (pair 𝒦 hij) := hW.trans (inf_le_inter_pair 𝒦 hij)
    have e1 : P (𝟙 A) 𝒦 c' hij W hW = (Scheme.Hom.appLE (𝟙 A) (𝒦.inter (pair 𝒦 hij)) W hW').hom (c' (pair 𝒦 hij)) := rfl
    rw [e1, id_appLE]
    refine (hNat (𝒦.inter (pair 𝒦 hij)) W hW' (c' (pair 𝒦 hij))).trans ?_
    rw [hc' (pair 𝒦 hij), map_sub]
    congr 1
    · show ((A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le (pair 𝒦 hij) 0))).op ≫
          A.presheaf.map (homOfLE (N.preimage_mono hW')).op)).hom (S' i) = _
      rw [← A.presheaf.map_comp]
      exact hΦ'eq _ _ rfl _ _ _
    · show ((A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le (pair 𝒦 hij) 1))).op ≫
          A.presheaf.map (homOfLE (N.preimage_mono hW')).op)).hom (S' j) = _
      rw [← A.presheaf.map_comp]
      exact hΦ'eq _ _ rfl _ _ _

  let Φ : ∀ (t : 𝒲.Idx 1) (j : Fin 2), Γ(A, N ⁻¹ᵁ 𝒲.inter t) := fun t j =>
    (φ.appLE (N ⁻¹ᵁ 𝒦.U (lam (t.1 j))) (N ⁻¹ᵁ 𝒲.inter t)
      ((N.preimage_mono (𝒲.inter_le t j)).trans (hpre (t.1 j)))).hom (S (lam (t.1 j)))
  let Φ' : ∀ (t : 𝒲.Idx 1) (j : Fin 2), Γ(A, N ⁻¹ᵁ 𝒲.inter t) := fun t j =>
    (A.presheaf.map (homOfLE ((N.preimage_mono (𝒲.inter_le t j)).trans (hpre' (t.1 j)))).op).hom (S' (lam' (t.1 j)))
  have hNZ : ∀ t : 𝒲.Idx 1,
      (N.app (𝒲.inter t)).hom (Z φ 𝒦 c (lam (t.1 0)) (lam (t.1 1)) (𝒲.inter t) (inter_le_two φ 𝒲 𝒦 lam hlam t)) = Φ t 0 - Φ t 1 := by
    intro t
    rcases lt_trichotomy (lam (t.1 0)) (lam (t.1 1)) with hlt | heq | hgt
    · rw [Z_of_lt φ 𝒦 c hlt, hNP hlt _ _ ((N.preimage_mono (𝒲.inter_le t 0)).trans (hpre (t.1 0)))
        ((N.preimage_mono (𝒲.inter_le t 1)).trans (hpre (t.1 1)))]
    · rw [Z_of_eq φ 𝒦 c heq, map_zero]
      exact (sub_eq_zero.mpr (hΦeq _ _ heq (N ⁻¹ᵁ 𝒲.inter t) _ _)).symm
    · rw [Z_of_gt φ 𝒦 c hgt, map_neg, hNP hgt _ _ ((N.preimage_mono (𝒲.inter_le t 1)).trans (hpre (t.1 1)))
        ((N.preimage_mono (𝒲.inter_le t 0)).trans (hpre (t.1 0)))]
      show -(Φ t 1 - Φ t 0) = Φ t 0 - Φ t 1
      abel
  have hNZ' : ∀ t : 𝒲.Idx 1,
      (N.app (𝒲.inter t)).hom (Z (𝟙 A) 𝒦 c' (lam' (t.1 0)) (lam' (t.1 1)) (𝒲.inter t) (inter_le_two (𝟙 A) 𝒲 𝒦 lam' hlam' t)) = Φ' t 0 - Φ' t 1 := by
    intro t
    rcases lt_trichotomy (lam' (t.1 0)) (lam' (t.1 1)) with hlt | heq | hgt
    · rw [Z_of_lt (𝟙 A) 𝒦 c' hlt, hNP' hlt _ _ ((N.preimage_mono (𝒲.inter_le t 0)).trans (hpre' (t.1 0)))
        ((N.preimage_mono (𝒲.inter_le t 1)).trans (hpre' (t.1 1)))]
    · rw [Z_of_eq (𝟙 A) 𝒦 c' heq, map_zero]
      exact (sub_eq_zero.mpr (hΦ'eq _ _ heq (N ⁻¹ᵁ 𝒲.inter t) _ _)).symm
    · rw [Z_of_gt (𝟙 A) 𝒦 c' hgt, map_neg, hNP' hgt _ _ ((N.preimage_mono (𝒲.inter_le t 1)).trans (hpre' (t.1 1)))
        ((N.preimage_mono (𝒲.inter_le t 0)).trans (hpre' (t.1 0)))]
      show -(Φ' t 1 - Φ' t 0) = Φ' t 0 - Φ' t 1
      abel

  have hNb : ∀ (t : 𝒲.Idx 1) (j : Fin 2),
      (N.app (𝒲.inter t)).hom ((A.presheaf.map (homOfLE (𝒲.inter_le t j)).op).hom (bt (t.1 j))) = Φ t j - Φ' t j := by
    intro t j
    rw [hNat, hbt, map_sub]
    congr 1
    · show (φ.appLE (N ⁻¹ᵁ 𝒦.U (lam (t.1 j))) (N ⁻¹ᵁ 𝒲.U (t.1 j)) (hpre (t.1 j)) ≫
          A.presheaf.map (homOfLE (N.preimage_mono (𝒲.inter_le t j))).op).hom (S (lam (t.1 j))) = _
      rw [Scheme.Hom.appLE_map]
    · show (A.presheaf.map (homOfLE (hpre' (t.1 j))).op ≫
          A.presheaf.map (homOfLE (N.preimage_mono (𝒲.inter_le t j))).op).hom (S' (lam' (t.1 j))) = _
      rw [← A.presheaf.map_comp]; rfl

  have hinjT : ∀ t : 𝒲.Idx 1, Function.Injective (N.app (𝒲.inter t)).hom := fun t =>
    hinj ⟨𝒲.inter t, isAffineOpen_inter K f hA 𝒲 t⟩

  refine ⟨-b, ?_⟩
  funext t
  apply hinjT t

  have hres0 : (OModulePresheaf.unit f).res (𝒲.inter_le_inter_face t 0) (b (𝒲.face t 0)) =
      (A.presheaf.map (homOfLE (𝒲.inter_le t 1)).op).hom (bt (t.1 1)) := by
    show (A.presheaf.map (homOfLE (𝒲.inter_le_inter_face t 0)).op).hom
      ((A.presheaf.map (homOfLE (𝒲.inter_le (𝒲.face t 0) 0)).op).hom (bt (t.1 1))) = _
    rw [← CommRingCat.comp_apply, ← A.presheaf.map_comp]
    rfl
  have hres1 : (OModulePresheaf.unit f).res (𝒲.inter_le_inter_face t 1) (b (𝒲.face t 1)) =
      (A.presheaf.map (homOfLE (𝒲.inter_le t 0)).op).hom (bt (t.1 0)) := by
    show (A.presheaf.map (homOfLE (𝒲.inter_le_inter_face t 1)).op).hom
      ((A.presheaf.map (homOfLE (𝒲.inter_le (𝒲.face t 1) 0)).op).hom (bt (t.1 0))) = _
    rw [← CommRingCat.comp_apply, ← A.presheaf.map_comp]
    rfl
  have hd : ((OModulePresheaf.unit f).d 𝒲 0 (-b)) t =
      -((A.presheaf.map (homOfLE (𝒲.inter_le t 1)).op).hom (bt (t.1 1)) -
        (A.presheaf.map (homOfLE (𝒲.inter_le t 0)).op).hom (bt (t.1 0))) := by
    rw [LinearMap.map_neg]
    show -(((OModulePresheaf.unit f).d 𝒲 0 b) t) = _
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
    rw [hres0, hres1, ← sub_eq_add_neg]
    rfl
  have L : (N.app (𝒲.inter t)).hom (((OModulePresheaf.unit f).d 𝒲 0 (-b)) t) = -((Φ t 1 - Φ' t 1) - (Φ t 0 - Φ' t 0)) := by
    rw [hd]
    simp only [map_neg, map_sub]
    rw [hNb t 1, hNb t 0]
  have hZ : (OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1 c -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1 c') t =
      Z φ 𝒦 c (lam (t.1 0)) (lam (t.1 1)) (𝒲.inter t) (inter_le_two φ 𝒲 𝒦 lam hlam t) -
        Z (𝟙 A) 𝒦 c' (lam' (t.1 0)) (lam' (t.1 1)) (𝒲.inter t) (inter_le_two (𝟙 A) 𝒲 𝒦 lam' hlam' t) := by
    rw [Pi.sub_apply, unitPullback_one_eq_Z f φ 𝒲 𝒦 lam hlam c t, unitPullback_one_eq_Z f (𝟙 A) 𝒲 𝒦 lam' hlam' c' t]
    rfl
  have R : (N.app (𝒲.inter t)).hom ((OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1 c -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1 c') t) = (Φ t 0 - Φ t 1) - (Φ' t 0 - Φ' t 1) := by
    rw [hZ]
    simp only [map_sub]
    rw [hNZ t, hNZ' t]
  rw [L, R]
  abel

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts (solution)
