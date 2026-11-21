-- Prove2me | solution 1 for LiuHelsenDesigns.OneD.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:32:48.325319+00:00
-- url     : https://prove2.me/submissions/528025a2-de7b-49ec-827d-67a1ce22dbc2

import Mathlib

/-!
# Classification of pairs of subspaces by the dimensions of the members and of their
intersection, together with the existence criterion for prescribed dimensions.

Everything is proved over an arbitrary field `K` and specialized at the end to `ZMod 2`.
-/

open Submodule

namespace LiuHelsenSubspacesAux

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `I ≤ U` and `V = I ⊕ W`, then `U = I ⊔ (U ⊓ W)`. -/
lemma sup_inf_eq_of_le_of_isCompl {I U W : Submodule K V} (hIU : I ≤ U) (h : IsCompl I W) :
    I ⊔ (U ⊓ W) = U := by
  refine le_antisymm (sup_le hIU inf_le_left) ?_
  intro u hu
  have hmem : u ∈ I ⊔ W := by rw [h.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨i, hi, w, hw, hsum⟩ := Submodule.mem_sup.mp hmem
  have hwU : w ∈ U := by
    have hsub : u - i ∈ U := Submodule.sub_mem U hu (hIU hi)
    have hw_eq : w = u - i := by rw [← hsum]; abel
    rw [hw_eq]; exact hsub
  exact Submodule.mem_sup.mpr ⟨i, hi, w, ⟨hwU, hw⟩, hsum⟩

/-- If `V = I ⊕ W`, then `I ⊓ (U ⊓ W) = ⊥`. -/
lemma inf_inf_eq_bot_of_isCompl {I U W : Submodule K V} (h : IsCompl I W) :
    I ⊓ (U ⊓ W) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx' : x ∈ I ⊓ W := ⟨hx.1, hx.2.2⟩
  rw [h.inf_eq_bot] at hx'
  exact hx'

/-- If `I = U ⊓ S` and `V = I ⊕ W`, then `(I ⊔ (U ⊓ W)) ⊓ (S ⊓ W) = ⊥`. -/
lemma sup_inf_inf_eq_bot {I U S W : Submodule K V} (hI : I = U ⊓ S) (h : IsCompl I W) :
    (I ⊔ (U ⊓ W)) ⊓ (S ⊓ W) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxIW, hxSW⟩ := hx
  rw [Submodule.mem_inf] at hxSW
  obtain ⟨hxS, hxW⟩ := hxSW
  obtain ⟨i, hi, u, hu, hsum⟩ := Submodule.mem_sup.mp hxIW
  have huW : u ∈ W := hu.2
  have hiW : i ∈ W := by
    have hsub : x - u ∈ W := Submodule.sub_mem W hxW huW
    have hi_eq : i = x - u := by rw [← hsum]; abel
    rw [hi_eq]; exact hsub
  have hi0 : i = 0 := by
    have hmem : i ∈ I ⊓ W := ⟨hi, hiW⟩
    rw [h.inf_eq_bot] at hmem
    simpa using hmem
  have hxU : x ∈ U := by
    rw [← hsum, hi0, zero_add]
    exact hu.1
  have hxI : x ∈ I := by
    rw [hI]
    exact ⟨hxU, hxS⟩
  have hmem : x ∈ I ⊓ W := ⟨hxI, hxW⟩
  rw [h.inf_eq_bot] at hmem
  simpa using hmem

/-- If `p ⊓ q = ⊥`, then `p × q` is linearly equivalent to `p ⊔ q` (internal direct sum). -/
noncomputable def prodEquivOfDisjoint {p q : Submodule K V} (h : p ⊓ q = ⊥) :
    (p × q) ≃ₗ[K] ↥(p ⊔ q) :=
  let f : (p × q) →ₗ[K] ↥(p ⊔ q) :=
    { toFun := fun x => ⟨(x.1 : V) + (x.2 : V), Submodule.add_mem_sup x.1.2 x.2.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
        abel
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }
  LinearEquiv.ofBijective f (by
    constructor
    · intro x y hxy
      have hval : (x.1 : V) + (x.2 : V) = (y.1 : V) + (y.2 : V) := congrArg Subtype.val hxy
      have hmem : (x.1 : V) - (y.1 : V) ∈ p ⊓ q := by
        constructor
        · exact Submodule.sub_mem p x.1.2 y.1.2
        · have step : (x.1 : V) - (y.1 : V) = (y.2 : V) - (x.2 : V) := by
            rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, hval, add_sub_cancel_left]
          rw [step]
          exact Submodule.sub_mem q y.2.2 x.2.2
      rw [h] at hmem
      have h1 : (x.1 : V) = (y.1 : V) := sub_eq_zero.mp hmem
      have h2 : (x.2 : V) = (y.2 : V) := by
        rw [h1] at hval
        exact add_left_cancel hval
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro y
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp y.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by simpa [f] using hab)⟩)

lemma prodEquivOfDisjoint_apply {p q : Submodule K V} (h : p ⊓ q = ⊥) (x : p × q) :
    ((prodEquivOfDisjoint h x : ↥(p ⊔ q)) : V) = (x.1 : V) + (x.2 : V) := rfl

section Finite

variable [FiniteDimensional K V]

/-- Two pairs of subspaces with equal dimensions of the members and of their intersections
are equivalent under a linear automorphism of the ambient space. -/
theorem pair_classification (U₁ U₂ S₁ S₂ : Submodule K V)
    (hU : Module.finrank K U₁ = Module.finrank K U₂)
    (hS : Module.finrank K S₁ = Module.finrank K S₂)
    (hI : Module.finrank K ↥(U₁ ⊓ S₁) = Module.finrank K ↥(U₂ ⊓ S₂)) :
    ∃ G : V ≃ₗ[K] V, U₁.map G.toLinearMap = U₂ ∧ S₁.map G.toLinearMap = S₂ := by
  classical
  obtain ⟨W₁, hW₁⟩ := Submodule.exists_isCompl (U₁ ⊓ S₁)
  obtain ⟨W₂, hW₂⟩ := Submodule.exists_isCompl (U₂ ⊓ S₂)
  set I₁ : Submodule K V := U₁ ⊓ S₁ with hI₁
  set I₂ : Submodule K V := U₂ ⊓ S₂ with hI₂
  set U₁' : Submodule K V := U₁ ⊓ W₁ with hU₁'
  set S₁' : Submodule K V := S₁ ⊓ W₁ with hS₁'
  set U₂' : Submodule K V := U₂ ⊓ W₂ with hU₂'
  set S₂' : Submodule K V := S₂ ⊓ W₂ with hS₂'
  obtain ⟨T₁, hT₁⟩ := Submodule.exists_isCompl (U₁ ⊔ S₁)
  obtain ⟨T₂, hT₂⟩ := Submodule.exists_isCompl (U₂ ⊔ S₂)
  -- basic inequalities
  have hI₁U₁ : I₁ ≤ U₁ := by rw [hI₁]; exact inf_le_left
  have hI₁S₁ : I₁ ≤ S₁ := by rw [hI₁]; exact inf_le_right
  have hI₂U₂ : I₂ ≤ U₂ := by rw [hI₂]; exact inf_le_left
  have hI₂S₂ : I₂ ≤ S₂ := by rw [hI₂]; exact inf_le_right
  have hW₁I : IsCompl I₁ W₁ := by rw [hI₁]; exact hW₁
  have hW₂I : IsCompl I₂ W₂ := by rw [hI₂]; exact hW₂
  -- decomposition of U and S along the intersection
  have hUdecomp : I₁ ⊔ U₁' = U₁ := by
    have h := sup_inf_eq_of_le_of_isCompl (I := I₁) (U := U₁) (W := W₁) hI₁U₁ hW₁I
    simpa [U₁'] using h
  have hSdecomp : I₁ ⊔ S₁' = S₁ := by
    have h := sup_inf_eq_of_le_of_isCompl (I := I₁) (U := S₁) (W := W₁) hI₁S₁ hW₁I
    simpa [S₁'] using h
  have hUdecomp₂ : I₂ ⊔ U₂' = U₂ := by
    have h := sup_inf_eq_of_le_of_isCompl (I := I₂) (U := U₂) (W := W₂) hI₂U₂ hW₂I
    simpa [U₂'] using h
  have hSdecomp₂ : I₂ ⊔ S₂' = S₂ := by
    have h := sup_inf_eq_of_le_of_isCompl (I := I₂) (U := S₂) (W := W₂) hI₂S₂ hW₂I
    simpa [S₂'] using h
  -- disjointness of the pieces
  have hIU₁ : I₁ ⊓ U₁' = ⊥ := by
    have h := inf_inf_eq_bot_of_isCompl (I := I₁) (U := U₁) (W := W₁) hW₁I
    simpa [U₁'] using h
  have hIU₂ : I₂ ⊓ U₂' = ⊥ := by
    have h := inf_inf_eq_bot_of_isCompl (I := I₂) (U := U₂) (W := W₂) hW₂I
    simpa [U₂'] using h
  have hIS₁ : I₁ ⊓ S₁' = ⊥ := by
    have h := inf_inf_eq_bot_of_isCompl (I := I₁) (U := S₁) (W := W₁) hW₁I
    simpa [S₁'] using h
  have hIS₂ : I₂ ⊓ S₂' = ⊥ := by
    have h := inf_inf_eq_bot_of_isCompl (I := I₂) (U := S₂) (W := W₂) hW₂I
    simpa [S₂'] using h
  have hIUS₁ : (I₁ ⊔ U₁') ⊓ S₁' = ⊥ := by
    have h := sup_inf_inf_eq_bot (I := I₁) (U := U₁) (S := S₁) (W := W₁) hI₁ hW₁I
    simpa [U₁', S₁'] using h
  have hIUS₂ : (I₂ ⊔ U₂') ⊓ S₂' = ⊥ := by
    have h := sup_inf_inf_eq_bot (I := I₂) (U := U₂) (S := S₂) (W := W₂) hI₂ hW₂I
    simpa [U₂', S₂'] using h
  have hP₁ : (I₁ ⊔ U₁') ⊔ S₁' = U₁ ⊔ S₁ := by
    rw [hUdecomp, ← hSdecomp, ← sup_assoc, sup_eq_left.mpr hI₁U₁]
  have hP₂ : (I₂ ⊔ U₂') ⊔ S₂' = U₂ ⊔ S₂ := by
    rw [hUdecomp₂, ← hSdecomp₂, ← sup_assoc, sup_eq_left.mpr hI₂U₂]
  have hT₁' : IsCompl ((I₁ ⊔ U₁') ⊔ S₁') T₁ := by
    rw [hP₁]; exact hT₁
  have hT₂' : IsCompl ((I₂ ⊔ U₂') ⊔ S₂') T₂ := by
    rw [hP₂]; exact hT₂
  -- dimension equations
  have hdimU₁ : Module.finrank K U₁ = Module.finrank K ↥I₁ + Module.finrank K ↥U₁' := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq I₁ U₁'
    rw [hUdecomp, hIU₁, finrank_bot, add_zero] at hdim
    omega
  have hdimU₂ : Module.finrank K U₂ = Module.finrank K ↥I₂ + Module.finrank K ↥U₂' := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq I₂ U₂'
    rw [hUdecomp₂, hIU₂, finrank_bot, add_zero] at hdim
    omega
  have hdimS₁ : Module.finrank K S₁ = Module.finrank K ↥I₁ + Module.finrank K ↥S₁' := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq I₁ S₁'
    rw [hSdecomp, hIS₁, finrank_bot, add_zero] at hdim
    exact hdim
  have hdimS₂ : Module.finrank K S₂ = Module.finrank K ↥I₂ + Module.finrank K ↥S₂' := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq I₂ S₂'
    rw [hSdecomp₂, hIS₂, finrank_bot, add_zero] at hdim
    exact hdim
  have hdimT₁ : Module.finrank K V = Module.finrank K ↥(U₁ ⊔ S₁) + Module.finrank K ↥T₁ := by
    have h1 : Module.finrank K (↥(U₁ ⊔ S₁) × ↥T₁) = Module.finrank K V :=
      LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl (U₁ ⊔ S₁) T₁ hT₁)
    rw [Module.finrank_prod] at h1
    omega
  have hdimT₂ : Module.finrank K V = Module.finrank K ↥(U₂ ⊔ S₂) + Module.finrank K ↥T₂ := by
    have h1 : Module.finrank K (↥(U₂ ⊔ S₂) × ↥T₂) = Module.finrank K V :=
      LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl (U₂ ⊔ S₂) T₂ hT₂)
    rw [Module.finrank_prod] at h1
    omega
  have hsup₁ : Module.finrank K ↥(U₁ ⊔ S₁) + Module.finrank K ↥I₁
      = Module.finrank K U₁ + Module.finrank K S₁ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U₁ S₁
    rwa [← hI₁] at h
  have hsup₂ : Module.finrank K ↥(U₂ ⊔ S₂) + Module.finrank K ↥I₂
      = Module.finrank K U₂ + Module.finrank K S₂ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U₂ S₂
    rwa [← hI₂] at h
  -- isomorphisms of the pieces
  have hdimI : Module.finrank K ↥I₁ = Module.finrank K ↥I₂ := by
    rw [hI₁, hI₂]; exact hI
  have hdimUp : Module.finrank K ↥U₁' = Module.finrank K ↥U₂' := by omega
  have hdimSp : Module.finrank K ↥S₁' = Module.finrank K ↥S₂' := by omega
  have hdimT : Module.finrank K ↥T₁ = Module.finrank K ↥T₂ := by omega
  let φ : ↥I₁ ≃ₗ[K] ↥I₂ := LinearEquiv.ofFinrankEq _ _ hdimI
  let α : ↥U₁' ≃ₗ[K] ↥U₂' := LinearEquiv.ofFinrankEq _ _ hdimUp
  let β : ↥S₁' ≃ₗ[K] ↥S₂' := LinearEquiv.ofFinrankEq _ _ hdimSp
  let γ : ↥T₁ ≃ₗ[K] ↥T₂ := LinearEquiv.ofFinrankEq _ _ hdimT
  -- the ambient block decompositions
  let eI₁ : (↥I₁ × ↥U₁') ≃ₗ[K] ↥(I₁ ⊔ U₁') := prodEquivOfDisjoint hIU₁
  let eIUS₁ : (↥(I₁ ⊔ U₁') × ↥S₁') ≃ₗ[K] ↥((I₁ ⊔ U₁') ⊔ S₁') := prodEquivOfDisjoint hIUS₁
  let eP₁ : (↥((I₁ ⊔ U₁') ⊔ S₁') × ↥T₁) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl ((I₁ ⊔ U₁') ⊔ S₁') T₁ hT₁'
  let e₁ : (((↥I₁ × ↥U₁') × ↥S₁') × ↥T₁) ≃ₗ[K] V :=
    (LinearEquiv.prodCongr (LinearEquiv.prodCongr eI₁ (LinearEquiv.refl K ↥S₁'))
        (LinearEquiv.refl K ↥T₁)).trans
      ((LinearEquiv.prodCongr eIUS₁ (LinearEquiv.refl K ↥T₁)).trans eP₁)
  let eI₂ : (↥I₂ × ↥U₂') ≃ₗ[K] ↥(I₂ ⊔ U₂') := prodEquivOfDisjoint hIU₂
  let eIUS₂ : (↥(I₂ ⊔ U₂') × ↥S₂') ≃ₗ[K] ↥((I₂ ⊔ U₂') ⊔ S₂') := prodEquivOfDisjoint hIUS₂
  let eP₂ : (↥((I₂ ⊔ U₂') ⊔ S₂') × ↥T₂) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl ((I₂ ⊔ U₂') ⊔ S₂') T₂ hT₂'
  let e₂ : (((↥I₂ × ↥U₂') × ↥S₂') × ↥T₂) ≃ₗ[K] V :=
    (LinearEquiv.prodCongr (LinearEquiv.prodCongr eI₂ (LinearEquiv.refl K ↥S₂'))
        (LinearEquiv.refl K ↥T₂)).trans
      ((LinearEquiv.prodCongr eIUS₂ (LinearEquiv.refl K ↥T₂)).trans eP₂)
  have e₁_apply : ∀ (i : ↥I₁) (u : ↥U₁') (s : ↥S₁') (t : ↥T₁),
      e₁ (((i, u), s), t) = (i : V) + (u : V) + (s : V) + (t : V) := by
    intro i u s t
    simp only [e₁, eI₁, eIUS₁, eP₁, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', prodEquivOfDisjoint_apply,
      Submodule.coe_add]
  have e₂_apply : ∀ (i : ↥I₂) (u : ↥U₂') (s : ↥S₂') (t : ↥T₂),
      e₂ (((i, u), s), t) = (i : V) + (u : V) + (s : V) + (t : V) := by
    intro i u s t
    simp only [e₂, eI₂, eIUS₂, eP₂, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', prodEquivOfDisjoint_apply,
      Submodule.coe_add]
  have e₁_symm_I : ∀ (i : ↥I₁), e₁.symm (i : V) = (((i, 0), 0), 0) := by
    intro i
    rw [LinearEquiv.symm_apply_eq, e₁_apply]
    simp
  have e₁_symm_U : ∀ (u : ↥U₁'), e₁.symm (u : V) = (((0, u), 0), 0) := by
    intro u
    rw [LinearEquiv.symm_apply_eq, e₁_apply]
    simp
  have e₁_symm_S : ∀ (s : ↥S₁'), e₁.symm (s : V) = (((0, 0), s), 0) := by
    intro s
    rw [LinearEquiv.symm_apply_eq, e₁_apply]
    simp
  -- the coordinate isomorphism
  let Φ : (((↥I₁ × ↥U₁') × ↥S₁') × ↥T₁) ≃ₗ[K] (((↥I₂ × ↥U₂') × ↥S₂') × ↥T₂) :=
    LinearEquiv.prodCongr (LinearEquiv.prodCongr (LinearEquiv.prodCongr φ α) β) γ
  let G : V ≃ₗ[K] V := e₁.symm.trans (Φ.trans e₂)
  have G_apply : ∀ x : V, G x = e₂ (Φ (e₁.symm x)) := by
    intro x; rfl
  have G_I : ∀ i : ↥I₁, G (i : V) = (φ i : V) := by
    intro i
    rw [G_apply, e₁_symm_I]
    simp [Φ, e₂_apply]
  have G_U : ∀ u : ↥U₁', G (u : V) = (α u : V) := by
    intro u
    rw [G_apply, e₁_symm_U]
    simp [Φ, e₂_apply]
  have G_S : ∀ s : ↥S₁', G (s : V) = (β s : V) := by
    intro s
    rw [G_apply, e₁_symm_S]
    simp [Φ, e₂_apply]
  -- `G` maps `U₁` into `U₂` and `S₁` into `S₂`
  have hmapU : U₁.map G.toLinearMap ≤ U₂ := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    have hx' : x ∈ I₁ ⊔ U₁' := by rw [hUdecomp]; exact hx
    obtain ⟨i, hi, u, hu, hsum⟩ := Submodule.mem_sup.mp hx'
    have hGx : G x = (φ ⟨i, hi⟩ : V) + (α ⟨u, hu⟩ : V) := by
      rw [← hsum, map_add, G_I ⟨i, hi⟩, G_U ⟨u, hu⟩]
    show G x ∈ U₂
    rw [hGx]
    have h12 : (φ ⟨i, hi⟩ : V) + (α ⟨u, hu⟩ : V) ∈ I₂ ⊔ U₂' :=
      Submodule.add_mem_sup (φ ⟨i, hi⟩).2 (α ⟨u, hu⟩).2
    rwa [hUdecomp₂] at h12
  have hmapS : S₁.map G.toLinearMap ≤ S₂ := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    have hx' : x ∈ I₁ ⊔ S₁' := by rw [hSdecomp]; exact hx
    obtain ⟨i, hi, s, hs, hsum⟩ := Submodule.mem_sup.mp hx'
    have hGx : G x = (φ ⟨i, hi⟩ : V) + (β ⟨s, hs⟩ : V) := by
      rw [← hsum, map_add, G_I ⟨i, hi⟩, G_S ⟨s, hs⟩]
    show G x ∈ S₂
    rw [hGx]
    have h12 : (φ ⟨i, hi⟩ : V) + (β ⟨s, hs⟩ : V) ∈ I₂ ⊔ S₂' :=
      Submodule.add_mem_sup (φ ⟨i, hi⟩).2 (β ⟨s, hs⟩).2
    rwa [hSdecomp₂] at h12
  refine ⟨G, ?_, ?_⟩
  · exact Submodule.eq_of_le_of_finrank_le hmapU (by
      rw [LinearEquiv.finrank_map_eq G U₁, hU])
  · exact Submodule.eq_of_le_of_finrank_le hmapS (by
      rw [LinearEquiv.finrank_map_eq G S₁, hS])

end Finite

section Part2

variable [FiniteDimensional K V]

/-- The intersection of the spans of two subsets of a basis is the span of the intersection. -/
lemma span_inter_span {ι : Type*} (b : Module.Basis ι K V) (A B : Set ι) :
    Submodule.span K (b '' (A ∩ B)) = Submodule.span K (b '' A) ⊓ Submodule.span K (b '' B) := by
  refine le_antisymm ?_ ?_
  · rw [le_inf_iff]
    exact ⟨Submodule.span_mono (Set.image_mono Set.inter_subset_left),
      Submodule.span_mono (Set.image_mono Set.inter_subset_right)⟩
  · intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Module.Basis.mem_span_image]
    exact Set.subset_inter
      (Module.Basis.repr_support_subset_of_mem_span b A hx.1)
      (Module.Basis.repr_support_subset_of_mem_span b B hx.2)

lemma part2_imp {r s j : ℕ}
    (h : ∃ U S : Submodule K V,
      Module.finrank K U = r ∧ Module.finrank K S = s ∧ Module.finrank K ↥(U ⊓ S) = j) :
    r + s ≤ Module.finrank K V + j ∧ j ≤ r ∧ j ≤ s := by
  obtain ⟨U, S, hU, hS, hI⟩ := h
  have h1 : Module.finrank K ↥(U ⊔ S) + Module.finrank K ↥(U ⊓ S)
      = Module.finrank K ↥U + Module.finrank K ↥S :=
    Submodule.finrank_sup_add_finrank_inf_eq U S
  have h2 : Module.finrank K ↥(U ⊔ S) ≤ Module.finrank K V := Submodule.finrank_le (U ⊔ S)
  have h3 : Module.finrank K ↥(U ⊓ S) ≤ Module.finrank K ↥U := Submodule.finrank_mono inf_le_left
  have h4 : Module.finrank K ↥(U ⊓ S) ≤ Module.finrank K ↥S := Submodule.finrank_mono inf_le_right
  omega

lemma part2_surj {r s j : ℕ}
    (h1 : r + s ≤ Module.finrank K V + j) (h2 : j ≤ r) (h3 : j ≤ s) :
    ∃ U S : Submodule K V,
      Module.finrank K U = r ∧ Module.finrank K S = s ∧ Module.finrank K ↥(U ⊓ S) = j := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, n = Module.finrank K V := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin n) K V) := by
    rw [hn]
    exact ⟨Module.finBasis K V⟩
  have hrn : r ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hrsn : r + (s - j) ≤ n := by omega
  let f : Fin r → Fin n := fun i => ⟨i.val, by omega⟩
  let g : Fin j ⊕ Fin (s - j) → Fin n := fun x =>
    match x with
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr k => ⟨r + k.val, by omega⟩
  let hJ : Fin j → Fin n := fun i => ⟨i.val, by omega⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    match x, y with
    | Sum.inl a, Sum.inl b =>
        have : a.val = b.val := by simpa [g] using congrArg Fin.val hxy
        exact congrArg Sum.inl (Fin.ext this)
    | Sum.inl a, Sum.inr k =>
        have hv : a.val = r + k.val := by simpa [g] using congrArg Fin.val hxy
        have := a.isLt
        omega
    | Sum.inr k, Sum.inl a =>
        have hv : r + k.val = a.val := by simpa [g] using congrArg Fin.val hxy
        have := a.isLt
        omega
    | Sum.inr k, Sum.inr k' =>
        have : k.val = k'.val := by simpa [g] using congrArg Fin.val hxy
        exact congrArg Sum.inr (Fin.ext this)
  have mem_f : ∀ x : Fin n, x ∈ Set.range f ↔ x.val < r := by
    intro x; constructor
    · rintro ⟨i, rfl⟩; exact i.isLt
    · intro hx; exact ⟨⟨x.val, hx⟩, by simp [f]⟩
  have mem_g : ∀ x : Fin n,
      x ∈ Set.range g ↔ x.val < j ∨ (r ≤ x.val ∧ x.val < r + (s - j)) := by
    intro x; constructor
    · rintro ⟨y, rfl⟩
      cases y with
      | inl i => exact Or.inl i.isLt
      | inr k =>
          right
          have := k.isLt
          constructor <;> simp [g] <;> omega
    · rintro (hx | ⟨hx1, hx2⟩)
      · exact ⟨Sum.inl ⟨x.val, hx⟩, by simp [g]⟩
      · refine ⟨Sum.inr ⟨x.val - r, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [g, Fin.val_mk]
        omega
  have mem_J : ∀ x : Fin n, x ∈ Set.range hJ ↔ x.val < j := by
    intro x; constructor
    · rintro ⟨i, rfl⟩; exact i.isLt
    · intro hx; exact ⟨⟨x.val, hx⟩, by simp [hJ]⟩
  have hAB : Set.range f ∩ Set.range g = Set.range hJ := by
    ext x
    rw [Set.mem_inter_iff, mem_f x, mem_g x, mem_J x]
    constructor
    · rintro ⟨h1, h2 | ⟨h3, h4⟩⟩
      · exact h2
      · omega
    · intro hx
      exact ⟨by omega, Or.inl hx⟩
  have hli_f : LinearIndependent K (fun i : Fin r => b (f i)) :=
    b.linearIndependent.comp f hf_inj
  have hli_g : LinearIndependent K (fun x : Fin j ⊕ Fin (s - j) => b (g x)) :=
    b.linearIndependent.comp g hg_inj
  have hli_J : LinearIndependent K (fun i : Fin j => b (hJ i)) :=
    b.linearIndependent.comp hJ (by
      intro a b hab
      exact Fin.ext (by simpa [hJ] using congrArg Fin.val hab))
  have hfr : Module.finrank K ↥(Submodule.span K (b '' Set.range f)) = r := by
    have := finrank_span_eq_card hli_f
    rwa [show Set.range (fun i : Fin r => b (f i)) = b '' Set.range f from Set.range_comp _ _,
      Fintype.card_fin] at this
  have hgs : Module.finrank K ↥(Submodule.span K (b '' Set.range g)) = s := by
    have := finrank_span_eq_card hli_g
    rw [show Set.range (fun x : Fin j ⊕ Fin (s - j) => b (g x)) = b '' Set.range g from
      Set.range_comp _ _, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel' h3] at this
    exact this
  have hJj : Module.finrank K ↥(Submodule.span K (b '' Set.range hJ)) = j := by
    have := finrank_span_eq_card hli_J
    rwa [show Set.range (fun i : Fin j => b (hJ i)) = b '' Set.range hJ from Set.range_comp _ _,
      Fintype.card_fin] at this
  refine ⟨Submodule.span K (b '' Set.range f), Submodule.span K (b '' Set.range g),
    hfr, hgs, ?_⟩
  rw [← span_inter_span b (Set.range f) (Set.range g), hAB, hJj]

end Part2

end LiuHelsenSubspacesAux

/-- Lemma 20: pairs of subspaces are classified up to a linear automorphism by the dimensions
of the two subspaces and of their intersection; and the triples of dimensions that occur are
exactly those satisfying `j ≤ r`, `j ≤ s` and `r + s ≤ dim V + j`. -/
theorem solution (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] :
    (∀ U₁ U₂ S₁ S₂ : Submodule (ZMod 2) V,
      Module.finrank (ZMod 2) U₁ = Module.finrank (ZMod 2) U₂ →
      Module.finrank (ZMod 2) S₁ = Module.finrank (ZMod 2) S₂ →
      Module.finrank (ZMod 2) ↥(U₁ ⊓ S₁) = Module.finrank (ZMod 2) ↥(U₂ ⊓ S₂) →
      ∃ G : V ≃ₗ[ZMod 2] V, U₁.map G.toLinearMap = U₂ ∧ S₁.map G.toLinearMap = S₂) ∧
    (∀ r s j : ℕ,
      (∃ U S : Submodule (ZMod 2) V,
        Module.finrank (ZMod 2) U = r ∧ Module.finrank (ZMod 2) S = s ∧
        Module.finrank (ZMod 2) ↥(U ⊓ S) = j) ↔
      r + s ≤ Module.finrank (ZMod 2) V + j ∧ j ≤ r ∧ j ≤ s) := by
  constructor
  · intro U₁ U₂ S₁ S₂ hU hS hI
    exact LiuHelsenSubspacesAux.pair_classification U₁ U₂ S₁ S₂ hU hS hI
  · intro r s j
    constructor
    · intro h
      exact LiuHelsenSubspacesAux.part2_imp (K := ZMod 2) (V := V) h
    · intro h
      exact LiuHelsenSubspacesAux.part2_surj (K := ZMod 2) (V := V) h.1 h.2.1 h.2.2
