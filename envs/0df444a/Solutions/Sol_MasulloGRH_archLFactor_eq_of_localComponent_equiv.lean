-- Prove2me | solution 1 for MasulloGRH.archLFactor_eq_of_localComponent_equiv
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:34:14.82632+00:00
-- url     : https://prove2.me/submissions/ee71261f-befe-4856-939d-03206e9aabe8

import Definitions.Def_MasulloGRH_CompletedL

set_option autoImplicit false
open scoped WithZero
open NumberField IsDedekindDomain

namespace MasulloGRH.CharTransport

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]

/-- the weight property -/
def WtP (χ : HeckeCharacter F) (w : InfinitePlace F) (n : ℤ) : Prop :=
  ∀ (x : w.Completionˣ), ‖(x : w.Completion)‖ = 1 →
    χ.localComponentInfinite w x =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n

lemma wtP_inv (χ : HeckeCharacter F) (w : InfinitePlace F) (n : ℤ) (h : WtP χ w n) :
    WtP χ⁻¹ w (-n) := by
  intro x hx
  have hi : ∀ g, (χ⁻¹) g = (χ g)⁻¹ := fun g => rfl
  have := h x hx
  unfold HeckeCharacter.localComponentInfinite at this ⊢
  rw [hi, Circle.coe_inv, this, zpow_neg]

lemma wtP_unique (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : ¬ w.IsReal) (n m : ℤ)
    (hn : WtP χ w n) (hm : WtP χ w m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  set ζ : ℂ := Complex.exp (Real.pi * Complex.I / ((n - m : ℤ) : ℂ))
  have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hwc ζ
  have hζn : ‖ζ‖ = 1 := by
    simp only [ζ, Complex.norm_exp]
    have : (Real.pi * Complex.I / ((n - m : ℤ) : ℂ)).re = 0 := by
      simp [Complex.div_re]
    rw [this, Real.exp_zero]
  have hyn : ‖y‖ = 1 := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) y, hy, hζn]
  have hy0 : y ≠ 0 := by intro h0; rw [h0, norm_zero] at hyn; norm_num at hyn
  have h1 := hn (Units.mk0 y hy0) hyn
  have h2 := hm (Units.mk0 y hy0) hyn
  rw [h1] at h2
  simp only [Units.val_mk0, hy] at h2
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have h3 : ζ ^ (n - m) = 1 := by
    rw [zpow_sub₀ hζ0, h2, div_self (zpow_ne_zero _ hζ0)]
  have h4 : ζ ^ (n - m) = -1 := by
    simp only [ζ]
    rw [← Complex.exp_int_mul, mul_div_cancel₀ _ hd, Complex.exp_pi_mul_I]
  rw [h3] at h4; norm_num at h4


lemma dite_choose_congr {α β : Type*} {P Q : α → Prop} {_i1 : Decidable (∃ a, P a)} {_i2 : Decidable (∃ a, Q a)}
    (f : α → β) (d : β) (h : ∀ a, P a ↔ Q a) :
    (if hp : ∃ a, P a then f hp.choose else d) = (if hq : ∃ a, Q a then f hq.choose else d) := by
  have : P = Q := funext fun a => propext (h a)
  subst this; congr

lemma ext_emb_norm (w : InfinitePlace F) (z : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w z‖ = ‖z‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

lemma units_neg_one_map {A B : Type*} [Field A] [Field B] (hA : (2 : A) ≠ 0) (κ : Aˣ ≃* Bˣ) :
    κ (-1) = -1 := by
  have h2 : (κ (-1)) * (κ (-1)) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h2' : ((κ (-1) : Bˣ) : B) * (κ (-1) : B) = 1 := by rw [← Units.val_mul, h2, Units.val_one]
  rcases mul_self_eq_one_iff.mp h2' with h | h
  · exfalso
    have : κ (-1) = κ 1 := by rw [map_one]; exact Units.ext h
    have := congrArg Units.val (κ.injective this)
    simp only [Units.val_neg, Units.val_one] at this
    apply hA; linear_combination -this
  · exact Units.ext (by simpa using h)

lemma completion_two_ne_zero (w : InfinitePlace F) : (2 : w.Completion) ≠ 0 := by
  intro h
  have := congrArg (InfinitePlace.Completion.extensionEmbedding w) h
  rw [map_ofNat, map_zero] at this; norm_num at this

/-- Γ-factor data is preserved by a compatible local isomorphism at an infinite place. -/
lemma archLFactor_transport (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (w : InfinitePlace F) (w' : InfinitePlace K) (κ : (w.Completion)ˣ ≃* (w'.Completion)ˣ)
    (hR : w'.IsReal ↔ w.IsReal)
    (hemb : (∀ x : (w.Completion)ˣ,
        InfinitePlace.Completion.extensionEmbedding w' (κ x : w'.Completion) =
          InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ∨
      (∀ x : (w.Completion)ˣ,
        InfinitePlace.Completion.extensionEmbedding w' (κ x : w'.Completion) =
          starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion))))
    (hloc : ∀ x, η.localComponentInfinite w' (κ x) = χ.localComponentInfinite w x) :
    η.archLFactor w' = χ.archLFactor w := by
  set e := InfinitePlace.Completion.extensionEmbedding w
  set e' := InfinitePlace.Completion.extensionEmbedding w'
  have hloc' : ∀ y, χ.localComponentInfinite w (κ.symm y) = η.localComponentInfinite w' y := fun y => by
    rw [← hloc, MulEquiv.apply_symm_apply]
  have hmult : w'.mult = w.mult := by
    unfold InfinitePlace.mult; by_cases h : w.IsReal
    · rw [if_pos h, if_pos (hR.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hR.mp h'))]
  have hnorm : ∀ x : (w.Completion)ˣ, ‖(κ x : w'.Completion)‖ = ‖(x : w.Completion)‖ := by
    intro x
    rw [← ext_emb_norm w', ← ext_emb_norm w]
    rcases hemb with h | h <;> rw [h x]; rw [Complex.norm_conj]
  have hre : ∀ x : (w.Completion)ˣ, (e' (κ x : w'.Completion)).re = (e (x : w.Completion)).re := by
    intro x; rcases hemb with h | h <;> rw [h x]; rw [Complex.conj_re]
  have him : ∀ x : (w.Completion)ˣ,
      (e' (κ x : w'.Completion)).im = 0 ↔ (e (x : w.Completion)).im = 0 := by
    intro x; rcases hemb with h | h <;> rw [h x]; rw [Complex.conj_im, neg_eq_zero]
  -- exponent
  have hexp : η.archExponent w' = χ.archExponent w := by
    unfold HeckeCharacter.archExponent
    refine dite_choose_congr (fun t : ℝ => t) (0 : ℝ) ?_
    intro t
    constructor
    · intro H x hx1 hx2
      have := H (κ x) ((him x).mpr hx1) (by rw [hre]; exact hx2)
      rw [hloc, hnorm, hmult] at this; exact this
    · intro H y hy1 hy2
      have hy : y = κ (κ.symm y) := (MulEquiv.apply_symm_apply κ y).symm
      rw [hy] at hy1 hy2 ⊢
      have := H (κ.symm y) ((him _).mp hy1) (by rw [← hre]; exact hy2)
      rw [hloc, hnorm, hmult]; exact this
  -- parity
  have hpar : η.archParity w' = χ.archParity w := by
    unfold HeckeCharacter.archParity
    rw [← units_neg_one_map (completion_two_ne_zero w) κ, hloc]
  -- weight (only matters at complex places)
  have hwt : ¬ w.IsReal → η.archWeight w' = χ.archWeight w := by
    intro hw
    have hw' : ¬ w'.IsReal := fun h => hw (hR.mp h)
    have gen : ∀ ε : ℤ → ℤ, (∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 → ∀ n : ℤ,
        e' (κ x : w'.Completion) ^ n = e (x : w.Completion) ^ (ε n)) →
        ∀ n, WtP η w' n ↔ WtP χ w (ε n) := by
      intro ε hε n
      constructor
      · intro H x hx
        have := H (κ x) (by rw [hnorm]; exact hx)
        rw [hloc, hε x hx] at this; exact this
      · intro H y hy
        have hy' : y = κ (κ.symm y) := (MulEquiv.apply_symm_apply κ y).symm
        rw [hy'] at hy ⊢
        rw [hnorm] at hy
        unfold WtP at H
        rw [hloc, hε _ hy]; exact H _ hy
    have key : (∀ n : ℤ, WtP η w' n ↔ WtP χ w n) ∨ (∀ n : ℤ, WtP η w' n ↔ WtP χ w (-n)) := by
      rcases hemb with h | h
      · left; exact gen id (fun x _ n => by rw [h x]; rfl)
      · right
        refine gen (fun n => -n) (fun x hx n => ?_)
        rw [h x]
        have hn1 : ‖e (x : w.Completion)‖ = 1 := by rw [ext_emb_norm]; exact hx
        have hc : starRingEnd ℂ (e (x : w.Completion)) = (e (x : w.Completion))⁻¹ := by
          rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn1]; simp
        rw [hc, inv_zpow', zpow_neg]
    unfold HeckeCharacter.archWeight
    split_ifs with h1 h2 h2
    · have s1 : WtP η w' h1.choose := h1.choose_spec
      have s2 : WtP χ w h2.choose := h2.choose_spec
      rcases key with k | k
      · rw [wtP_unique χ w hw _ _ ((k _).mp s1) s2]
      · rw [← wtP_unique χ w hw _ _ ((k _).mp s1) s2, Int.natAbs_neg]
    · exfalso; apply h2
      rcases key with k | k
      · exact ⟨_, (k _).mp h1.choose_spec⟩
      · exact ⟨_, (k _).mp h1.choose_spec⟩
    · exfalso; apply h1
      rcases key with k | k
      · exact ⟨_, (k _).mpr h2.choose_spec⟩
      · exact ⟨-h2.choose, (k _).mpr (by rw [neg_neg]; exact h2.choose_spec)⟩
    · rfl
  funext s
  unfold HeckeCharacter.archLFactor
  by_cases h : w.IsReal
  · rw [if_pos (hR.mpr h), if_pos h, hexp, hpar]
  · rw [if_neg (fun h' => h (hR.mp h')), if_neg h, hexp, hwt h]

end MasulloGRH.CharTransport

open MasulloGRH MasulloGRH.CharTransport in
theorem solution
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (ψ : HeckeCharacter K) (v : InfinitePlace F) (w : InfinitePlace K)
    (a : v.Completion ≃+* w.Completion)
    (hreal : v.IsReal ↔ w.IsReal)
    (hemb : ∃ conjugate : Bool, ∀ x : v.Completion,
      InfinitePlace.Completion.extensionEmbedding w (a x) =
        if conjugate then star (InfinitePlace.Completion.extensionEmbedding v x)
        else InfinitePlace.Completion.extensionEmbedding v x)
    (hlocal : ∀ x : (v.Completion)ˣ,
      χ.localComponentInfinite v x = ψ.localComponentInfinite w (Units.map a.toMonoidHom x)) :
    χ.archLFactor v = ψ.archLFactor w := by
  obtain ⟨c, hc⟩ := hemb
  set κ : (v.Completion)ˣ ≃* (w.Completion)ˣ := Units.mapEquiv a.toMulEquiv
  have hκ : ∀ x, κ x = Units.map a.toMonoidHom x := fun x => Units.ext rfl
  have hκv : ∀ x : (v.Completion)ˣ, ((κ x : (w.Completion)ˣ) : w.Completion) = a x := fun x => rfl
  have hemb' : (∀ x : (v.Completion)ˣ,
        InfinitePlace.Completion.extensionEmbedding w (κ x : w.Completion) =
          InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ∨
      (∀ x : (v.Completion)ˣ,
        InfinitePlace.Completion.extensionEmbedding w (κ x : w.Completion) =
          starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion))) := by
    cases c
    · left; intro x; rw [hκv, hc x]; rfl
    · right; intro x; rw [hκv, hc x]; rfl
  exact (archLFactor_transport χ ψ v w κ hreal.symm hemb'
    (fun x => by rw [hκ]; exact (hlocal x).symm)).symm
