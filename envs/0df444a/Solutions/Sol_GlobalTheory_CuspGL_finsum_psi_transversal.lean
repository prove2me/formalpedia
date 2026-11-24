-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_psi_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:02.315286+00:00
-- url     : https://prove2.me/submissions/3b6c6bce-4b91-471b-89e3-d37abde0d6dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspaces
import Theorems.Thm_GlobalTheory_CuspGL_charpoly_eq_finsum_psi
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
open Polynomial in
private lemma card_nilRad_eq_card_linearMap_quot (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module F V] (A : Submodule F V) :
    Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) = Nat.card ((V ⧸ A) →ₗ[F] A) := by
  refine Nat.card_congr
    { toFun := fun n => A.liftQ (LinearMap.codRestrict A n.1 n.2.1) (fun a ha => by
          simp [LinearMap.mem_ker, n.2.2 a ha])
      invFun := fun h => ⟨A.subtype ∘ₗ h ∘ₗ A.mkQ, fun x => by simp, fun x hx => by
          simp [(Submodule.Quotient.mk_eq_zero A).2 hx]⟩
      left_inv := fun n => by ext x; simp
      right_inv := fun h => by ext x; simp }
open Polynomial in
private lemma card_invariant_complements_over_eq_card_nilRad (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) (U : Submodule F (V ⧸ A)) (hU : ∀ y ∈ U, A.mapQ A g hg y ∈ U) :
    Nat.card {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} =
      Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) := by
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype A)
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective A.mkQ (Submodule.range_mkQ A)
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  let gU : U →ₗ[F] U := (A.mapQ A g hg).restrict hU
  let D : (U →ₗ[F] A) → (U →ₗ[F] V) := fun τ => σ ∘ₗ U.subtype ∘ₗ gU + A.subtype ∘ₗ τ ∘ₗ gU -
    g ∘ₗ σ ∘ₗ U.subtype - g ∘ₗ A.subtype ∘ₗ τ
  have hDA : ∀ τ u, D τ u ∈ A := by
    intro τ u
    rw [← Submodule.Quotient.mk_eq_zero]
    have h1 : ∀ q, A.mkQ (σ q) = q := fun q => LinearMap.congr_fun hσ q
    have h2 : ∀ a : A, A.mkQ (g a) = 0 := fun a => (Submodule.Quotient.mk_eq_zero A).2 (hg a a.2)
    have h3 : A.mkQ (g (σ u)) = A.mapQ A g hg u := by
      conv_rhs => rw [← h1 u]
      rfl
    simp only [D, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add]
    have := h1 (gU u)
    have h4 := h2 (τ u)
    have h5 := h2 (τ (gU u))
    simp only [Submodule.mkQ_apply] at this h4 h5 h3 ⊢
    rw [this, h3, h4]
    simp [gU]
  have hp' : ∀ u : U, p u = u := fun u => LinearMap.congr_fun hp u
  let E : (V ⧸ A) →ₗ[F] (V ⧸ A) := U.subtype ∘ₗ p
  have hS : Nat.card {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1} =
      Nat.card ((V ⧸ A) →ₗ[F] A) := by
    refine Nat.card_congr
      { toFun := fun q => q.1.1 ∘ₗ p + q.1.2 ∘ₗ (LinearMap.id - E)
        invFun := fun h => ⟨(h ∘ₗ U.subtype, ρ ∘ₗ D (h ∘ₗ U.subtype) ∘ₗ p + h ∘ₗ (LinearMap.id - E)),
          by ext u; simp [E, hp']⟩
        left_inv := fun q => ?_
        right_inv := fun h => ?_ }
    · have h1 : (q.1.1 ∘ₗ p + q.1.2 ∘ₗ (LinearMap.id - E)) ∘ₗ U.subtype = q.1.1 := by
        ext u; simp [E, hp']
      refine Subtype.ext (Prod.ext h1 ?_)
      simp only [h1]
      ext x
      have h2 := LinearMap.congr_fun q.2 (p (Submodule.Quotient.mk x))
      simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h2
      simp [E, hp', ← h2]
    · ext x
      simp [E, hp']
  have hρ' : ∀ v ∈ A, (ρ v : V) = v := fun v hv => congrArg Subtype.val (LinearMap.congr_fun hρ ⟨v, hv⟩)
  have hσ' : ∀ q : V ⧸ A, A.mkQ (σ q) = q := fun q => LinearMap.congr_fun hσ q
  have hmapQ : ∀ v : V, A.mkQ (g v) = A.mapQ A g hg (A.mkQ v) := fun v => rfl
  let Γ : (U →ₗ[F] A) → (U →ₗ[F] V) := fun τ => σ ∘ₗ U.subtype + A.subtype ∘ₗ τ
  have hΓ : ∀ τ (u : U), A.mkQ (Γ τ u) = u := by
    intro τ u
    simp only [Γ, LinearMap.add_apply, LinearMap.comp_apply, map_add, hσ']
    simp [(Submodule.Quotient.mk_eq_zero A).2 (τ u).2]
  have memN : ∀ k : (V ⧸ A) →ₗ[F] A, A.subtype ∘ₗ k ∘ₗ A.mkQ ∈ _root_.GlobalTheory.CuspGL.nilRad A :=
    fun k => ⟨fun x => by simp, fun x hx => by simp [(Submodule.Quotient.mk_eq_zero A).2 hx]⟩
  have botΓ : ∀ τ, LinearMap.range (Γ τ) ⊓ A = ⊥ := by
    intro τ
    rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, hx⟩
    have h0 : (u : V ⧸ A) = 0 := by rw [← hΓ τ u]; exact (Submodule.Quotient.mk_eq_zero A).2 hx
    have hu : u = 0 := Subtype.ext h0
    rw [hu, map_zero]
    exact Submodule.zero_mem _
  have mapΓ : ∀ τ, (LinearMap.range (Γ τ)).map A.mkQ = U := by
    intro τ
    rw [← LinearMap.range_comp]
    have : A.mkQ ∘ₗ Γ τ = U.subtype := by ext u; exact hΓ τ u
    rw [this, Submodule.range_subtype]
  have invΓ : ∀ q : {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1},
      ∀ v ∈ LinearMap.range (Γ q.1.1),
        (g + A.subtype ∘ₗ q.1.2 ∘ₗ A.mkQ) v ∈ LinearMap.range (Γ q.1.1) := by
    rintro q _ ⟨u, rfl⟩
    refine ⟨gU u, ?_⟩
    have h2 : (q.1.2 (A.mkQ (Γ q.1.1 u)) : V) = D q.1.1 u := by
      rw [hΓ]
      have := LinearMap.congr_fun q.2 u
      simp only [LinearMap.comp_apply, Submodule.coe_subtype] at this
      rw [this, hρ' _ (hDA _ _)]
    change _ = g (Γ q.1.1 u) + (q.1.2 (A.mkQ (Γ q.1.1 u)) : V)
    rw [h2]
    simp only [D, Γ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, map_add]
    abel
  let Φ : {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1} →
      {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
        x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} :=
    fun q => ⟨(A.subtype ∘ₗ q.1.2 ∘ₗ A.mkQ, LinearMap.range (Γ q.1.1)), memN _, botΓ _, invΓ q,
      mapΓ _⟩
  have hinjΦ : Function.Injective Φ := by
    intro q q' h
    have h1 := congrArg (fun x => x.1.1) h
    have h2 := congrArg (fun x => x.1.2) h
    simp only [Φ] at h1 h2
    have e2 : q.1.2 = q'.1.2 := by
      ext x
      simpa using LinearMap.congr_fun h1 x
    have e1 : q.1.1 = q'.1.1 := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      have hu : Γ q.1.1 u ∈ LinearMap.range (Γ q'.1.1) := h2 ▸ ⟨u, rfl⟩
      obtain ⟨u', hu'⟩ := hu
      have hu'' : u' = u := Subtype.ext (by rw [← hΓ q'.1.1 u', hu', hΓ])
      subst hu''
      simp only [Γ, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        add_right_inj] at hu'
      exact hu'.symm
    exact Subtype.ext (Prod.ext e1 e2)
  have hsurjΦ : Function.Surjective Φ := by
    rintro ⟨⟨n, W⟩, hn, hbot, hinv, hmap⟩
    have hinj : Function.Injective (A.mkQ.comp W.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, eq_bot_iff]
      rintro ⟨x, hxW⟩ hxA
      have hx : x ∈ W ⊓ A := ⟨hxW, hxA⟩
      rw [hbot] at hx
      simpa using hx
    have hrange : LinearMap.range (A.mkQ.comp W.subtype) = U := by
      rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
    let e : W ≃ₗ[F] U := (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
    have he : ∀ u : U, A.mkQ (e.symm u : V) = u :=
      fun u => congrArg Subtype.val (e.apply_symm_apply u)
    let τ : U →ₗ[F] A := LinearMap.codRestrict A (W.subtype ∘ₗ e.symm.toLinearMap - σ ∘ₗ U.subtype)
      (fun u => (Submodule.Quotient.mk_eq_zero A).1 (by
        have h1 := he u
        have h2 := hσ' u
        simp only [Submodule.mkQ_apply] at h1 h2
        simp [Submodule.Quotient.mk_sub, h1, h2]))
    have hΓτ : ∀ u, Γ τ u = e.symm u := by
      intro u; simp [Γ, τ]
    have hW : LinearMap.range (Γ τ) = W := by
      ext v
      constructor
      · rintro ⟨u, rfl⟩
        rw [hΓτ]
        exact (e.symm u).2
      · intro hv
        exact ⟨e ⟨v, hv⟩, by rw [hΓτ, e.symm_apply_apply]⟩
    let k : (V ⧸ A) →ₗ[F] A := A.liftQ (LinearMap.codRestrict A n hn.1) (fun a ha => by
      simp [LinearMap.mem_ker, hn.2 a ha])
    have hk : A.subtype ∘ₗ k ∘ₗ A.mkQ = n := by ext x; simp [k]
    have hcond : k ∘ₗ U.subtype = ρ ∘ₗ D τ := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [hρ' _ (hDA τ u)]
      have hk' : (k (u : V ⧸ A) : V) = n (Γ τ u) := by
        conv_lhs => rw [← hΓ τ u]
        exact LinearMap.congr_fun hk (Γ τ u)
      have hmemu : Γ τ u ∈ W := by rw [hΓτ]; exact (e.symm u).2
      have hmemg : Γ τ (gU u) ∈ W := by rw [hΓτ]; exact (e.symm (gU u)).2
      have hgn : (g + n) (Γ τ u) = Γ τ (gU u) := by
        have := @hinj ⟨_, hinv _ hmemu⟩ ⟨_, hmemg⟩ (by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply]
          rw [hΓ, LinearMap.add_apply, map_add, hmapQ, hΓ,
            show A.mkQ (n (Γ τ u)) = 0 from (Submodule.Quotient.mk_eq_zero A).2 (hn.1 _), add_zero]
          rfl)
        exact congrArg Subtype.val this
      rw [hk']
      rw [LinearMap.add_apply] at hgn
      rw [eq_sub_of_add_eq' hgn]
      simp only [D, Γ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, map_add]
      abel
    exact ⟨⟨(τ, k), hcond⟩, Subtype.ext (Prod.ext hk hW)⟩
  rw [card_nilRad_eq_card_linearMap_quot, ← hS]
  exact (Nat.card_eq_of_bijective Φ ⟨hinjΦ, hsurjΦ⟩).symm
open Polynomial in
private lemma psi_restrict_complement_eq_psi_quotient (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) (n : Module.End F V) (hn : n ∈ _root_.GlobalTheory.CuspGL.nilRad A)
    (W : Submodule F V) (hWA : W ⊓ A = ⊥) (hW : ∀ v ∈ W, (g + n) v ∈ W)
    (hU : ∀ y ∈ W.map A.mkQ, A.mapQ A g hg y ∈ W.map A.mkQ) :
    _root_.GlobalTheory.CuspGL.psi s W ((g + n).restrict hW) =
      _root_.GlobalTheory.CuspGL.psi s (W.map A.mkQ) ((A.mapQ A g hg).restrict hU) := by
  have hinj : Function.Injective (A.mkQ.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxA
    have hx : x ∈ W ⊓ A := ⟨hxW, hxA⟩
    rw [hWA] at hx
    simpa using hx
  have hrange : LinearMap.range (A.mkQ.comp W.subtype) = W.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let e : W ≃ₗ[F] W.map A.mkQ := (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  rw [← _root_.GlobalTheory.CuspGL.psi_conj F s _ _ e]
  congr 1
  ext y
  obtain ⟨w, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.restrict_apply]
  simp [e, hn.1 w.1]
end GlobalTheory.CuspGL
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
open Polynomial
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, _root_.GlobalTheory.CuspGL.psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
  intro F _ _ V _ _ _ s A g hg
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ⧸ A) := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun U : Submodule F V => (U : Set V)) SetLike.coe_injective
  haveI : Finite (Submodule F (V ⧸ A)) :=
    Finite.of_injective (fun U : Submodule F (V ⧸ A) => (U : Set (V ⧸ A))) SetLike.coe_injective
  set gb := A.mapQ A g (fun x hx => hg x hx) with hgb
  have hcount : ∀ (U : Submodule F (V ⧸ A)), (∀ y ∈ U, gb y ∈ U) →
      Nat.card {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
        x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} =
        Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) :=
    fun U hU => card_invariant_complements_over_eq_card_nilRad F V A g hg U hU
  have hstep : ∀ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2},
      ∀ y ∈ x.1.2.map A.mkQ, gb y ∈ x.1.2.map A.mkQ := by
    intro x y hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨(g + x.1.1) w, x.2.2.2 w hw, ?_⟩
    have h1 : A.mkQ (x.1.1 w) = 0 := (Submodule.Quotient.mk_eq_zero A).2 (x.2.1.1 w)
    simp only [LinearMap.add_apply, map_add, h1, add_zero]
    rfl
  have hpsi : ∀ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2},
      _root_.GlobalTheory.CuspGL.psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) =
        _root_.GlobalTheory.CuspGL.psi s (x.1.2.map A.mkQ) (gb.restrict (hstep x)) :=
    fun x => psi_restrict_complement_eq_psi_quotient F V s A g hg x.1.1 x.2.1 x.1.2 x.2.2.1 x.2.2.2
      (hstep x)
  let fib : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2} → {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U} :=
    fun x => ⟨_, hstep x⟩
  let G : {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U} → ℂ :=
    fun U => _root_.GlobalTheory.CuspGL.psi s U.1 (gb.restrict U.2)
  haveI := Fintype.ofFinite {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U}
  haveI := Fintype.ofFinite {x : Module.End F V × Submodule F V //
    x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}
  rw [_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F (V ⧸ A) s gb, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.mul_sum]
  simp_rw [hpsi]
  change ∑ x, G (fib x) = ∑ U, _ * G U
  rw [← Finset.sum_fiberwise Finset.univ fib (fun x => G (fib x))]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => G U) (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hequiv : {x // fib x = U} ≃ {x : Module.End F V × Submodule F V //
      x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧
        x.2.map A.mkQ = U.1} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, congrArg Subtype.val x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1⟩, Subtype.ext y.2.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← hcount U.1 U.2, ← Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
