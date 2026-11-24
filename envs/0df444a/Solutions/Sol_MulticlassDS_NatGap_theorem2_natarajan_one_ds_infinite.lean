-- Prove2me | solution 1 for MulticlassDS.NatGap.theorem2_natarajan_one_ds_infinite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:28:09.85435+00:00
-- url     : https://prove2.me/submissions/fe4d99d2-6842-4763-9ef8-044508801597
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Theorems.Thm_MulticlassDS_NatGap_pseudo_cube_natarajan_one

open MulticlassDS.NatGap

theorem P2M_nshatter_inj {X Y : Type} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X)
    (hS : NShatters H S) : Function.Injective S := by
  obtain ⟨f, g, hfg, hc⟩ := hS
  intro i j hij
  by_contra hne
  obtain ⟨h1, -, e1⟩ := hc (fun _ => true)
  obtain ⟨h2, -, e2⟩ := hc (fun k => decide (k = i))
  have a1 : h1 (S i) = f i := by simpa using congrFun e1 i
  have a2 : h1 (S j) = f j := by simpa using congrFun e1 j
  have b1 : h2 (S i) = f i := by simpa using congrFun e2 i
  have b2 : h2 (S j) = g j := by simpa [Ne.symm hne] using congrFun e2 j
  exact hfg j (a2.symm.trans ((congrArg h1 hij.symm).trans
    (a1.trans (b1.symm.trans ((congrArg h2 hij).trans b2)))))

theorem P2M_one_le_natarajan {X Y : Type} (H : Set (X → Y)) (h g : X → Y) (hh : h ∈ H)
    (hg : g ∈ H) (x : X) (hne : g x ≠ h x) : (1 : ℕ∞) ≤ natarajanDim H := by
  have hS : NShatters H (fun _ : Fin 1 => x) := by
    refine ⟨fun _ => g x, fun _ => h x, fun _ => hne, fun c => ?_⟩
    by_cases hc : c 0
    · refine ⟨g, hg, ?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [hc]
    · refine ⟨h, hh, ?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [hc]
  unfold natarajanDim
  exact le_trans (by simp) (le_iSup_of_le 1 (le_iSup_of_le _ (le_iSup_of_le hS le_rfl)))

theorem solution :
    ∃ (X Y : Type) (H : Set (X → Y)), natarajanDim H = 1 ∧ dsDim H = ⊤ := by
  have key : ∀ d : ℕ, ∃ (Y : Type) (B : Set (Fin (d + 1) → Y)),
      IsPseudoCube B ∧ natarajanDim B = 1 :=
    fun d => pseudo_cube_natarajan_one (d + 1) (by omega)
  choose Yf Bf hP hN using key
  obtain ⟨E, hE⟩ : ∃ E : (d : ℕ) → (Fin (d + 1) → Yf d) → (Σ d : ℕ, Fin (d + 1)) →
      Option (Σ d : ℕ, Yf d), ∀ d h d' (i : Fin (d' + 1)),
        E d h ⟨d', i⟩ = if e : d' = d then some ⟨d, h (Fin.cast (by rw [e]) i)⟩ else none :=
    ⟨fun d h x => if e : x.1 = d then some ⟨d, h (Fin.cast (by rw [e]) x.2)⟩ else none,
      fun _ _ _ _ => rfl⟩
  have hE1 : ∀ d h (i : Fin (d + 1)), E d h ⟨d, i⟩ = some ⟨d, h i⟩ := by
    intro d h i
    rw [hE]
    simp
  have hE2 : ∀ d h d' (i : Fin (d' + 1)), d' ≠ d → E d h ⟨d', i⟩ = none := by
    intro d h d' i hd
    rw [hE]
    simp [hd]
  clear hE
  let H : Set ((Σ d : ℕ, Fin (d + 1)) → Option (Σ d : ℕ, Yf d)) :=
    {φ | ∃ d, ∃ h ∈ Bf d, φ = E d h}
  have F1 : ∀ φ ∈ H, ∀ D (p : Fin (D + 1)), φ ⟨D, p⟩ ≠ none →
      ∃ h ∈ Bf D, (∀ r, φ ⟨D, r⟩ = some ⟨D, h r⟩) ∧
        ∀ D' (r : Fin (D' + 1)), D' ≠ D → φ ⟨D', r⟩ = none := by
    rintro φ ⟨d, h, hh, rfl⟩ D p hne
    have hDd : D = d := by
      by_contra hc
      exact hne (hE2 _ _ _ _ hc)
    subst hDd
    exact ⟨h, hh, fun r => hE1 _ _ _, fun D' r hD => hE2 _ _ _ _ hD⟩
  refine ⟨Σ d : ℕ, Fin (d + 1), Option (Σ d : ℕ, Yf d), H, le_antisymm ?_ ?_, ?_⟩
  · -- upper bound
    unfold natarajanDim
    refine iSup_le fun n => iSup_le fun S => iSup_le fun hS => ?_
    by_contra hn
    have hn2 : 2 ≤ n := by
      by_contra h
      exact hn (by exact_mod_cast (by omega : n ≤ 1))
    have hinj := P2M_nshatter_inj H S hS
    obtain ⟨f, g, hfg, hc⟩ := hS
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hi : i1 ≠ i0 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    have hx : S i1 ≠ S i0 := fun h => hi (hinj h)
    have Q : ∀ a b : Bool, ∃ φ ∈ H, φ (S i0) = (if a then f i0 else g i0) ∧
        φ (S i1) = (if b then f i1 else g i1) := by
      intro a b
      obtain ⟨φ, hφ, e⟩ := hc (fun i => if i = i0 then a else b)
      refine ⟨φ, hφ, ?_, ?_⟩
      · simpa using congrFun e i0
      · simpa [hi] using congrFun e i1
    have h0 := hfg i0
    have h1 := hfg i1
    generalize f i0 = u0 at Q h0
    generalize g i0 = v0 at Q h0
    generalize f i1 = u1 at Q h1
    generalize g i1 = v1 at Q h1
    rcases hS0 : S i0 with ⟨D, p⟩
    rcases hS1 : S i1 with ⟨D', q⟩
    rw [hS0, hS1] at hx
    rw [hS0, hS1] at Q
    obtain ⟨a, ha⟩ : ∃ a : Bool, (if a then u0 else v0) ≠ none := by
      by_cases hu : u0 = none
      · exact ⟨false, by simpa using fun hv => h0 (hu.trans hv.symm)⟩
      · exact ⟨true, by simpa using hu⟩
    have hDD : D' = D := by
      by_contra hD
      obtain ⟨φ, hφ, e0, e1⟩ := Q a true
      obtain ⟨φ', hφ', e0', e1'⟩ := Q a false
      obtain ⟨-, -, -, hz⟩ := F1 φ hφ D p (by rw [e0]; exact ha)
      obtain ⟨-, -, -, hz'⟩ := F1 φ' hφ' D p (by rw [e0']; exact ha)
      have z1 := hz D' q hD
      have z2 := hz' D' q hD
      rw [e1] at z1
      rw [e1'] at z2
      simp at z1 z2
      exact h1 (z1.trans z2.symm)
    subst hDD
    have hb : ∀ b : Bool, (if b then u1 else v1) ≠ none := by
      intro b
      obtain ⟨φ, hφ, e0, e1⟩ := Q a b
      obtain ⟨h, -, hs, -⟩ := F1 φ hφ _ p (by rw [e0]; exact ha)
      rw [← e1, hs q]
      simp
    have R : ∀ a b : Bool, ∃ h ∈ Bf D', some (⟨D', h p⟩ : Σ d : ℕ, Yf d) = (if a then u0 else v0) ∧
        some (⟨D', h q⟩ : Σ d : ℕ, Yf d) = (if b then u1 else v1) := by
      intro a' b'
      obtain ⟨φ, hφ, e0, e1⟩ := Q a' b'
      obtain ⟨h, hh, hs, -⟩ := F1 φ hφ _ q (by rw [e1]; exact hb b')
      exact ⟨h, hh, by rw [← hs p, e0], by rw [← hs q, e1]⟩
    obtain ⟨htt, mtt, ett0, ett1⟩ := R true true
    obtain ⟨hff, mff, eff0, eff1⟩ := R false false
    obtain ⟨htf, mtf, etf0, etf1⟩ := R true false
    obtain ⟨hft, mft, eft0, eft1⟩ := R false true
    simp only [if_true, Bool.false_eq_true, if_false] at ett0 ett1 eff0 eff1 etf0 etf1 eft0 eft1
    have c1 : htf p = htt p := by simpa using etf0.trans ett0.symm
    have c2 : htf q = hff q := by simpa using etf1.trans eff1.symm
    have c3 : hft p = hff p := by simpa using eft0.trans eff0.symm
    have c4 : hft q = htt q := by simpa using eft1.trans ett1.symm
    have n0 : htt p ≠ hff p := by
      intro e
      apply h0
      rw [← ett0, ← eff0, e]
    have n1 : htt q ≠ hff q := by
      intro e
      apply h1
      rw [← ett1, ← eff1, e]
    have hsh : NShatters (Bf D') ![p, q] := by
      refine ⟨![htt p, htt q], ![hff p, hff q],
        Fin.forall_fin_two.2 ⟨by simpa using n0, by simpa using n1⟩, fun c => ?_⟩
      rcases hc0 : c 0 with _ | _ <;> rcases hc1 : c 1 with _ | _
      · exact ⟨hff, mff, funext (Fin.forall_fin_two.2 ⟨by simp [hc0], by simp [hc1]⟩)⟩
      · exact ⟨hft, mft, funext (Fin.forall_fin_two.2 ⟨by simp [hc0, c3], by simp [hc1, c4]⟩)⟩
      · exact ⟨htf, mtf, funext (Fin.forall_fin_two.2 ⟨by simp [hc0, c1], by simp [hc1, c2]⟩)⟩
      · exact ⟨htt, mtt, funext (Fin.forall_fin_two.2 ⟨by simp [hc0], by simp [hc1]⟩)⟩
    have h2 : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [Nat.cast_one, ← hN D']
      unfold natarajanDim
      exact le_iSup_of_le 2 (le_iSup_of_le _ (le_iSup_of_le hsh le_rfl))
    have := Nat.cast_le.mp h2
    omega
  · -- lower bound
    obtain ⟨⟨w, hw⟩, -, hnb⟩ := hP 0
    obtain ⟨g, hg, hne, -⟩ := hnb w hw 0
    refine P2M_one_le_natarajan H (E 0 w) (E 0 g) ⟨0, w, hw, rfl⟩ ⟨0, g, hg, rfl⟩ ⟨0, 0⟩ ?_
    rw [hE1, hE1]
    simpa using hne
  · -- DS dimension
    have hle : ∀ d : ℕ, ((d + 1 : ℕ) : ℕ∞) ≤ dsDim H := by
      intro d
      have hsh : DSShatters H (fun i : Fin (d + 1) => (⟨d, i⟩ : Σ d : ℕ, Fin (d + 1))) := by
        refine ⟨(fun w : Fin (d + 1) → Yf d => fun i => some (⟨d, w i⟩ : Σ d : ℕ, Yf d)) '' Bf d,
          ?_, ?_⟩
        · rintro _ ⟨w, hw, rfl⟩
          refine ⟨E d w, ⟨d, w, hw, rfl⟩, ?_⟩
          funext i
          simp [hE1]
        · obtain ⟨hne, hfin, hnb⟩ := hP d
          refine ⟨hne.image _, hfin.image _, ?_⟩
          rintro _ ⟨w, hw, rfl⟩ i
          obtain ⟨g, hg, hgi, hgj⟩ := hnb w hw i
          refine ⟨_, ⟨g, hg, rfl⟩, by simpa using hgi, fun j hj => ?_⟩
          simp [hgj j hj]
      unfold dsDim
      exact le_iSup_of_le (d + 1) (le_iSup_of_le _ (le_iSup_of_le hsh le_rfl))
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have := hle m
    rw [← hm] at this
    have := Nat.cast_le.mp this
    omega
