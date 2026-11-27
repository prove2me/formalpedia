-- Prove2me | solution 1 for NumInvQH.Oblique.Supplement.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:56.391578+00:00
-- url     : https://prove2.me/submissions/85f4adee-22da-42be-8a83-fea466fbfe2f

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Complex

open Matrix

open NumInvQH
open NumInvQH.Oblique
open NumInvQH.Oblique.Supplement

/-- The complete complex statement of Theorem A.2, including directness of the kernel sum. -/
theorem solution {n p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (U : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin q) (Fin n) ℂ)
    (P : Matrix (Fin p) (Fin q) ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsComplexMoorePenrose (V * U) P)
    (hQ : IsComplexMoorePenrose (U * U.conjTranspose) Q)
    (hR : IsComplexMoorePenrose (V.conjTranspose * V) R) :
    let E := U * P * V
    let W := complexImage R (hermitianPerp (complexRange U ⊔ complexNull V))
    E * E = E ∧
    complexRange E = complexRange (U * U.conjTranspose * V.conjTranspose) ∧
    complexRange E = complexRange (U * U.conjTranspose * V.conjTranspose * V) ∧
    complexRange E = complexRange U ⊓
      hermitianPerp (complexImage Q (complexRange U ⊓ complexNull V)) ∧
    complexNull E = complexNull (U.conjTranspose * V.conjTranspose * V) ∧
    complexNull E = complexNull (U * U.conjTranspose * V.conjTranspose * V) ∧
    complexNull E = complexNull V ⊔ W ∧
    Disjoint (complexNull V) W := by
      dsimp only
      obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
      obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := hQ
      obtain ⟨hR1, hR2, hR3, hR4⟩ := hR
      -- general helpers
      have memR : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (x : Fin m → ℂ),
          x ∈ complexRange A ↔ ∃ y, A *ᵥ y = x := by
        intro m k A x; simp [complexRange, Matrix.toLin'_apply]
      have memN : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (x : Fin k → ℂ),
          x ∈ complexNull A ↔ A *ᵥ x = 0 := by
        intro m k A x; simp [complexNull, Matrix.toLin'_apply]
      have memI : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (S : Submodule ℂ (Fin k → ℂ))
          (x : Fin m → ℂ), x ∈ complexImage A S ↔ ∃ y ∈ S, A *ᵥ y = x := by
        intro m k A S x; simp [complexImage, Matrix.toLin'_apply]
      have memP : ∀ {m : ℕ} (S : Submodule ℂ (Fin m → ℂ)) (x : Fin m → ℂ),
          x ∈ hermitianPerp S ↔ ∀ y ∈ S, star y ⬝ᵥ x = 0 := fun S x => Iff.rfl
      have hdot : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (x : Fin m → ℂ) (y : Fin k → ℂ),
          star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
        intro m k A x y
        rw [Matrix.star_mulVec, conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]
      have hrng : ∀ {m k l : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (B : Matrix (Fin m) (Fin l) ℂ)
          (X : Matrix (Fin l) (Fin k) ℂ), A = B * X → complexRange A ≤ complexRange B := by
        intro m k l A B X h x hx
        obtain ⟨y, rfl⟩ := (memR _ _).1 hx
        exact (memR _ _).2 ⟨X *ᵥ y, by rw [h, Matrix.mulVec_mulVec]⟩
      have hnul : ∀ {m k l : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (B : Matrix (Fin l) (Fin k) ℂ)
          (X : Matrix (Fin m) (Fin l) ℂ), A = X * B → complexNull B ≤ complexNull A := by
        intro m k l A B X h x hx
        rw [memN] at hx ⊢
        rw [h, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      have L1' : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (G : Matrix (Fin m) (Fin m) ℂ),
          A * Aᴴ * G * (A * Aᴴ) = A * Aᴴ → A * Aᴴ * G * A = A := by
        intro m k A G h
        set X := A - A * Aᴴ * G * A with hX
        have h1 : X * Aᴴ = 0 := by
          rw [hX, Matrix.sub_mul,
            show A * Aᴴ * G * A * Aᴴ = A * Aᴴ * G * (A * Aᴴ) by simp only [Matrix.mul_assoc], h,
            sub_self]
        have h2 : Xᴴ = Aᴴ - Aᴴ * Gᴴ * (A * Aᴴ) := by
          rw [hX, conjTranspose_sub]
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        have h3 : X * Xᴴ = 0 := by
          rw [h2, Matrix.mul_sub]
          simp only [← Matrix.mul_assoc, h1, Matrix.zero_mul, sub_zero]
        have h4 : X = 0 := by open ComplexOrder in exact self_mul_conjTranspose_eq_zero.mp h3
        rw [hX, sub_eq_zero] at h4
        exact h4.symm
      have L1 : ∀ {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (G : Matrix (Fin k) (Fin k) ℂ),
          Aᴴ * A * G * (Aᴴ * A) = Aᴴ * A → A * G * (Aᴴ * A) = A := by
        intro m k A G h
        set X := A - A * G * (Aᴴ * A) with hX
        have h1 : Aᴴ * X = 0 := by
          rw [hX, Matrix.mul_sub,
            show Aᴴ * (A * G * (Aᴴ * A)) = Aᴴ * A * G * (Aᴴ * A) by simp only [Matrix.mul_assoc], h,
            sub_self]
        have h2 : Xᴴ = Aᴴ - Aᴴ * A * Gᴴ * Aᴴ := by
          rw [hX, conjTranspose_sub]
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        have h3 : Xᴴ * X = 0 := by
          rw [h2, Matrix.sub_mul]
          simp only [Matrix.mul_assoc, h1, Matrix.mul_zero, sub_zero]
        have h4 : X = 0 := by open ComplexOrder in exact conjTranspose_mul_self_eq_zero.mp h3
        rw [hX, sub_eq_zero] at h4
        exact h4.symm
      -- matrix identities
      have hE2 : U * P * V * (U * P * V) = U * P * V := by
        calc U * P * V * (U * P * V) = U * (P * (V * U) * P) * V := by simp only [Matrix.mul_assoc]
          _ = U * P * V := by rw [hP2]
      have hb : P = P * Pᴴ * Uᴴ * Vᴴ := by
        calc P = P * (V * U) * P := hP2.symm
          _ = P * (V * U * P) := by simp only [Matrix.mul_assoc]
          _ = P * (V * U * P)ᴴ := by rw [hP3]
          _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      have hc : P = Uᴴ * Vᴴ * Pᴴ * P := by
        calc P = P * (V * U) * P := hP2.symm
          _ = (P * (V * U))ᴴ * P := by rw [hP4]
          _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      have hd : Pᴴ = V * U * P * Pᴴ := by
        calc Pᴴ = (P * Pᴴ * Uᴴ * Vᴴ)ᴴ := by rw [← hb]
          _ = _ := by simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      have he : Uᴴ * Vᴴ = Uᴴ * Vᴴ * (V * U * P) := by
        calc Uᴴ * Vᴴ = (V * U)ᴴ := by rw [conjTranspose_mul]
          _ = (V * U * P * (V * U))ᴴ := by rw [hP1]
          _ = _ := by rw [conjTranspose_mul (V * U * P) (V * U), hP3, conjTranspose_mul]
      have hf : Uᴴ * Vᴴ * Pᴴ = P * (V * U) := by
        calc Uᴴ * Vᴴ * Pᴴ = (P * (V * U))ᴴ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = _ := hP4
      have F1 : U * P * V = U * Uᴴ * Vᴴ * (Pᴴ * P * V) := by
        calc U * P * V = U * (Uᴴ * Vᴴ * Pᴴ * P) * V := by rw [← hc]
          _ = _ := by simp only [Matrix.mul_assoc]
      have F2 : U * Uᴴ * Vᴴ = U * P * V * (U * Uᴴ * Vᴴ) := by
        symm
        calc U * P * V * (U * Uᴴ * Vᴴ) = U * (P * (V * U)) * (Uᴴ * Vᴴ) := by
              simp only [Matrix.mul_assoc]
          _ = U * (Uᴴ * Vᴴ * Pᴴ) * (Uᴴ * Vᴴ) := by rw [hf]
          _ = U * (Uᴴ * Vᴴ * (V * U * P)ᴴ) := by
              simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = U * (Uᴴ * Vᴴ * (V * U * P)) := by rw [hP3]
          _ = U * (Uᴴ * Vᴴ) := by rw [← he]
          _ = U * Uᴴ * Vᴴ := by simp only [Matrix.mul_assoc]
      have F3 : U * P * V = U * Uᴴ * Vᴴ * V * (U * P * Pᴴ * P * V) := by
        calc U * P * V = U * Uᴴ * Vᴴ * (Pᴴ * P * V) := F1
          _ = U * Uᴴ * Vᴴ * ((V * U * P * Pᴴ) * P * V) := by rw [← hd]
          _ = _ := by simp only [Matrix.mul_assoc]
      have F4 : U * Uᴴ * Vᴴ * V = U * P * V * (U * Uᴴ * Vᴴ * V) := by
        calc U * Uᴴ * Vᴴ * V = (U * P * V * (U * Uᴴ * Vᴴ)) * V := by rw [← F2]
          _ = _ := by simp only [Matrix.mul_assoc]
      have N1 : Uᴴ * Vᴴ * V = Uᴴ * Vᴴ * V * (U * P * V) := by
        calc Uᴴ * Vᴴ * V = Uᴴ * Vᴴ * (V * U * P) * V := by rw [← he]
          _ = _ := by simp only [Matrix.mul_assoc]
      have N2 : U * P * V = (U * P * Pᴴ) * (Uᴴ * Vᴴ * V) := by
        calc U * P * V = U * (P * Pᴴ * Uᴴ * Vᴴ) * V := by rw [← hb]
          _ = _ := by simp only [Matrix.mul_assoc]
      have hUQ : U * Uᴴ * Q * U = U := L1' U Q hQ1
      have hUQ' : Uᴴ = Uᴴ * Qᴴ * (U * Uᴴ) := by
        calc Uᴴ = (U * Uᴴ * Q * U)ᴴ := by rw [hUQ]
          _ = _ := by simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      have N3 : Uᴴ * Vᴴ * V = (Uᴴ * Qᴴ) * (U * Uᴴ * Vᴴ * V) := by
        calc Uᴴ * Vᴴ * V = (Uᴴ * Qᴴ * (U * Uᴴ)) * Vᴴ * V := by rw [← hUQ']
          _ = _ := by simp only [Matrix.mul_assoc]
      have hVR : V * R * (Vᴴ * V) = V := L1 V R hR1
      have hVR2 : V * (Vᴴ * V * R) = V := by
        have h0 : Vᴴ * Vᴴᴴ * R * (Vᴴ * Vᴴᴴ) = Vᴴ * Vᴴᴴ := by
          simpa only [conjTranspose_conjTranspose] using hR1
        have h' : Vᴴ * Vᴴᴴ * R * Vᴴ = Vᴴ := L1' Vᴴ R h0
        rw [conjTranspose_conjTranspose] at h'
        calc V * (Vᴴ * V * R) = V * (Vᴴ * V * R)ᴴ := by rw [hR3]
          _ = (Vᴴ * V * R * Vᴴ)ᴴ := by
              simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
          _ = V := by rw [h', conjTranspose_conjTranspose]
      have hfix : ∀ a, (U * Uᴴ) *ᵥ (Q *ᵥ (U *ᵥ a)) = U *ᵥ a := by
        intro a
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUQ]
      have hstar0 : ∀ {m : ℕ} (v : Fin m → ℂ), star v ⬝ᵥ v = 0 → v = 0 := by
        intro m v h
        open ComplexOrder in exact dotProduct_star_self_eq_zero.mp h
      have hwfix : ∀ w ∈ hermitianPerp (complexRange U ⊔ complexNull V),
          (Vᴴ * V * R) *ᵥ w = w := by
        intro w hw
        obtain ⟨u, hu⟩ : ∃ u, u = w - (Vᴴ * V * R) *ᵥ w := ⟨_, rfl⟩
        have hVu : V *ᵥ u = 0 := by
          rw [hu, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hVR2, sub_self]
        have hVVu : (Vᴴ * V) *ᵥ u = 0 := by
          rw [← Matrix.mulVec_mulVec, hVu, Matrix.mulVec_zero]
        have h1 : star u ⬝ᵥ w = 0 :=
          (memP _ _).1 hw u (Submodule.mem_sup_right ((memN _ _).2 hVu))
        have h2 : star u ⬝ᵥ ((Vᴴ * V * R) *ᵥ w) = 0 := by
          rw [← Matrix.mulVec_mulVec, hdot, conjTranspose_mul, conjTranspose_conjTranspose, hVVu,
            star_zero, zero_dotProduct]
        have h3 : star u ⬝ᵥ u = 0 := by
          calc star u ⬝ᵥ u = star u ⬝ᵥ (w - (Vᴴ * V * R) *ᵥ w) := by rw [← hu]
            _ = 0 := by rw [dotProduct_sub, h1, h2, sub_zero]
        have h4 := hstar0 u h3
        rw [hu, sub_eq_zero] at h4
        exact h4.symm
      have hUw : ∀ w ∈ hermitianPerp (complexRange U ⊔ complexNull V), Uᴴ *ᵥ w = 0 := by
        intro w hw
        apply hstar0
        rw [hdot, conjTranspose_conjTranspose]
        exact (memP _ _).1 hw _ (Submodule.mem_sup_left ((memR _ _).2 ⟨_, rfl⟩))
      -- conjuncts
      have c5 : complexNull (U * P * V) = complexNull (Uᴴ * Vᴴ * V) :=
        le_antisymm (hnul _ _ _ N1) (hnul _ _ _ N2)
      have c4le : complexRange (U * P * V) ≤ complexRange U ⊓
          hermitianPerp (complexImage Q (complexRange U ⊓ complexNull V)) := by
        intro x hx
        obtain ⟨z, rfl⟩ := (memR _ _).1 hx
        refine Submodule.mem_inf.2 ⟨(memR _ _).2 ⟨P *ᵥ (V *ᵥ z), by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]⟩, ?_⟩
        rw [memP]
        intro y hy
        obtain ⟨y0, hy0, rfl⟩ := (memI _ _ _).1 hy
        obtain ⟨hy0U, hy0V⟩ := Submodule.mem_inf.1 hy0
        obtain ⟨a, rfl⟩ := (memR _ _).1 hy0U
        rw [memN] at hy0V
        have hz : (U * P * V) *ᵥ z = (U * Uᴴ) *ᵥ (Vᴴ *ᵥ ((Pᴴ * P * V) *ᵥ z)) := by
          rw [F1]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hz, hdot, conjTranspose_mul, conjTranspose_conjTranspose, hfix, hdot,
          conjTranspose_conjTranspose, hy0V, star_zero, zero_dotProduct]
      have c4 : complexRange (U * P * V) = complexRange U ⊓
          hermitianPerp (complexImage Q (complexRange U ⊓ complexNull V)) := by
        refine le_antisymm c4le ?_
        intro x hx
        obtain ⟨hxU, hxP⟩ := Submodule.mem_inf.1 hx
        obtain ⟨a, rfl⟩ := (memR _ _).1 hxU
        rw [memP] at hxP
        obtain ⟨b, hb'⟩ : ∃ b, b = a - (P * (V * U)) *ᵥ a := ⟨_, rfl⟩
        have hy0 : U *ᵥ b = U *ᵥ a - (U * P * V) *ᵥ (U *ᵥ a) := by
          rw [hb', Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
          simp only [Matrix.mul_assoc]
        have hVy : V *ᵥ (U *ᵥ b) = 0 := by
          rw [hb', Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
            show V * U * (P * (V * U)) = V * U * P * (V * U) by simp only [Matrix.mul_assoc], hP1,
            sub_self]
        have hmem : Q *ᵥ (U *ᵥ b) ∈ complexImage Q (complexRange U ⊓ complexNull V) :=
          (memI _ _ _).2 ⟨_, Submodule.mem_inf.2 ⟨(memR _ _).2 ⟨b, rfl⟩, (memN _ _).2 hVy⟩, rfl⟩
        have t1 := hxP _ hmem
        have hEx : (U * P * V) *ᵥ (U *ᵥ a) ∈ complexRange U ⊓
            hermitianPerp (complexImage Q (complexRange U ⊓ complexNull V)) :=
          c4le ((memR _ _).2 ⟨_, rfl⟩)
        have t2 := (memP _ _).1 (Submodule.mem_inf.1 hEx).2 _ hmem
        have t3 : star (Q *ᵥ (U *ᵥ b)) ⬝ᵥ (U *ᵥ b) = 0 := by
          have e := congrArg (fun v => star (Q *ᵥ (U *ᵥ b)) ⬝ᵥ v) hy0
          rw [e, dotProduct_sub, t1, t2, sub_zero]
        have t4 : Uᴴ *ᵥ (Q *ᵥ (U *ᵥ b)) = 0 := by
          apply hstar0
          rw [← hdot, Matrix.mulVec_mulVec (M := U) (N := Uᴴ), hfix]
          exact t3
        have t5 : U *ᵥ b = 0 := by
          rw [← hfix b, ← Matrix.mulVec_mulVec, t4, Matrix.mulVec_zero]
        rw [hy0, sub_eq_zero] at t5
        exact (memR _ _).2 ⟨_, t5.symm⟩
      refine ⟨hE2, le_antisymm (hrng _ _ _ F1) (hrng _ _ _ F2),
        le_antisymm (hrng _ _ _ F3) (hrng _ _ _ F4), c4, c5, ?_, ?_, ?_⟩
      · rw [c5]
        exact le_antisymm (hnul (U * Uᴴ * Vᴴ * V) (Uᴴ * Vᴴ * V) U (by simp only [Matrix.mul_assoc]))
          (hnul _ _ _ N3)
      · rw [c5]
        apply le_antisymm
        · intro x hx
          rw [memN] at hx
          have hw : (Vᴴ * V) *ᵥ x ∈ hermitianPerp (complexRange U ⊔ complexNull V) := by
            rw [memP]
            intro y hy
            obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
            obtain ⟨a, rfl⟩ := (memR _ _).1 hy1
            rw [memN] at hy2
            rw [star_add, add_dotProduct]
            have t1 := hdot Uᴴ a ((Vᴴ * V) *ᵥ x)
            rw [conjTranspose_conjTranspose] at t1
            rw [← t1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hx, dotProduct_zero, zero_add,
              ← Matrix.mulVec_mulVec, hdot, conjTranspose_conjTranspose, hy2, star_zero,
              zero_dotProduct]
          refine Submodule.mem_sup.2 ⟨x - (R * (Vᴴ * V)) *ᵥ x, (memN _ _).2 ?_,
            R *ᵥ ((Vᴴ * V) *ᵥ x), (memI _ _ _).2 ⟨_, hw, rfl⟩, ?_⟩
          · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hVR, sub_self]
          · rw [Matrix.mulVec_mulVec, sub_add_cancel]
        · refine sup_le (hnul _ _ (Uᴴ * Vᴴ) rfl) ?_
          intro x hx
          obtain ⟨w, hw, rfl⟩ := (memI _ _ _).1 hx
          rw [memN]
          calc (Uᴴ * Vᴴ * V) *ᵥ (R *ᵥ w) = Uᴴ *ᵥ ((Vᴴ * V * R) *ᵥ w) := by
                simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
            _ = Uᴴ *ᵥ w := by rw [hwfix w hw]
            _ = 0 := hUw w hw
      · rw [Submodule.disjoint_def]
        intro x hxV hxW
        obtain ⟨w, hw, rfl⟩ := (memI _ _ _).1 hxW
        rw [memN] at hxV
        have : w = 0 := by
          calc w = (Vᴴ * V * R) *ᵥ w := (hwfix w hw).symm
            _ = Vᴴ *ᵥ (V *ᵥ (R *ᵥ w)) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
            _ = 0 := by rw [hxV, Matrix.mulVec_zero]
        rw [this, Matrix.mulVec_zero]
