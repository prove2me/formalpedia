-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFormalCoordinates_comp_adicEval_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a11975fb-4a44-5191-ae5d-aff417a90c60

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom.GoodReductionJacobian"
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff constantCoeff_subst_eq_zero)

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "FormalCoordinates IsFormalCoordinates"
namespace TransportCoords
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Nil

variable {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C]

theorem isAdicComplete_of_pow_eq_bot (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥) : IsAdicComplete J C := by
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx M
    rw [hM] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f M, fun m => by
    by_cases hm : m ≤ M
    · exact hf hm
    · push Not at hm
      have h1 : f M ≡ f m [SMOD (J ^ M • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = M + (m - M) by omega, pow_add, hM, Ideal.bot_mul]; simp
      have h3 : (J ^ M • ⊤ : Submodule C C) = ⊥ := by rw [hM]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem isNilpotent_of_mem {J : Ideal C} {n : ℕ} (hJ : J ^ (n + 1) = ⊥) {x : C} (hx : x ∈ J) : IsNilpotent x := by
  refine ⟨n + 1, ?_⟩
  have : x ^ (n + 1) ∈ J ^ (n + 1) := Ideal.pow_mem_pow hx _
  rw [hJ] at this
  exact (Submodule.mem_bot C).1 this

theorem pow_succ_eq_bot_of_le {J J₀ : Ideal C} {n : ℕ} (hJ : J ^ (n + 1) = ⊥) (hle : J₀ ≤ J) : J₀ ^ (n + 1) = ⊥ :=
  le_bot_iff.1 (hJ ▸ Ideal.pow_right_mono hle (n + 1))

theorem exists_span_range_pow_succ_eq_bot {g : ℕ} (s : Fin g → C) (hs : ∀ i, IsNilpotent (s i)) :
    ∃ n : ℕ, (Ideal.span (Set.range s)) ^ (n + 1) = ⊥ := by
  have hfg : (Ideal.span (Set.range s)).FG := ⟨(Set.finite_range s).toFinset, by simp⟩
  have hle : Ideal.span (Set.range s) ≤ nilradical C := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_nilradical.mpr (hs i)
  obtain ⟨k, hk⟩ := (hfg.isNilpotent_iff_le_nilradical).mpr hle
  refine ⟨k, ?_⟩
  rw [pow_succ, hk]
  simp

theorem nilEval_mem {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C) (n : ℕ)
    (φ : MvPowerSeries σ R) (hφ : constantCoeff φ = 0) (s : σ → C) (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s ∈ J := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    have : MvPolynomial.coeff 0 (MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm fun _ => n) φ) = 0 := by
      rw [MvPowerSeries.coeff_trunc', if_pos (show (0 : σ →₀ ℕ) ≤ Finsupp.equivFunOnFinite.symm (fun _ => n) from bot_le),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
    rw [this, map_zero, zero_mul]
    exact Ideal.zero_mem _
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd (Finsupp.ext hcon)
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    refine Ideal.mul_mem_left _ _ ?_
    rw [← Finset.mul_prod_erase _ _ hmem]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_mem_of_mem J (hs i) _ (Nat.pos_of_ne_zero hi)

theorem nilEval_X {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : σ → C) (hs : ∀ i, s i ∈ J) (i : σ) :
    MvFormalGroup.nilEval n (MvPowerSeries.X i : MvPowerSeries σ R) s = s i := by
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs, MvFormalGroup.adicEval_X]

theorem nilEval_natural {σ : Type} [Fintype σ] [DecidableEq σ] {C' : Type} [CommRing C'] [Algebra R C']
    (φ : C →ₐ[R] C') (n : ℕ) (f : MvPowerSeries σ R) (x : σ → C) :
    φ (MvFormalGroup.nilEval n f x) = MvFormalGroup.nilEval n f (φ ∘ x) := by
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem nilEval_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (a : τ → MvPowerSeries σ R) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries τ R) (x : σ → C) (hx : ∀ i, x i ∈ J) :
    MvFormalGroup.nilEval n (subst a f) x = MvFormalGroup.nilEval n f (fun j => MvFormalGroup.nilEval n (a j) x) := by
  haveI : IsAdicComplete J C := isAdicComplete_of_pow_eq_bot J hJ
  have hxr : ∀ i, x i ∈ J.radical := fun i => Ideal.le_radical (hx i)
  have hmem : ∀ j, MvFormalGroup.nilEval n (a j) x ∈ J := fun j => nilEval_mem J n (a j) (ha j) x hx
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ x hx,
    MvFormalGroup.adicEval_subst J hxr (hasSubst_of_constantCoeff_zero ha) f,
    MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ f _ hmem]
  congr 1
  funext j
  exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ (a j) x hx).symm

theorem forall_sumElim {M : Type} {p : M → Prop} {g : ℕ} {x y : Fin g → M} (hx : ∀ i, p (x i)) (hy : ∀ i, p (y i)) :
    ∀ c, p (Sum.elim x y c) := by
  rintro (i | i)
  exacts [hx i, hy i]

theorem nilMul_mem {g : ℕ} (F : MvFormalGroup g R) (J : Ideal C) (n : ℕ) (s t : Fin g → C)
    (hs : ∀ i, s i ∈ J) (ht : ∀ i, t i ∈ J) (i : Fin g) : F.nilMul n s t i ∈ J :=
  nilEval_mem J n _ (F.constantCoeff_eq_zero i) _ (forall_sumElim hs ht)

theorem nilEval_hom_nilMul {g g' : ℕ} {F : MvFormalGroup g R} {G : MvFormalGroup g' R} (h : MvFormalGroup.Hom F G)
    (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (s t : Fin g → C) (hs : ∀ i, s i ∈ J) (ht : ∀ i, t i ∈ J) :
    (fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) (F.nilMul n s t)) =
      G.nilMul n (fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) s)
        (fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) t) := by
  haveI : IsAdicComplete J C := isAdicComplete_of_pow_eq_bot J hJ
  let x : MvFormalGroup.Points F C J := ⟨s, fun i => Ideal.le_radical (hs i)⟩
  let y : MvFormalGroup.Points F C J := ⟨t, fun i => Ideal.le_radical (ht i)⟩
  have key := congrArg MvFormalGroup.Points.val (map_add h.evalPoints x y)
  have hst : ∀ c, Sum.elim s t c ∈ J := forall_sumElim hs ht
  have hFst : ∀ i, F.nilMul n s t i ∈ J := nilMul_mem F J n s t hs ht
  have hhs : ∀ i, MvFormalGroup.nilEval n (h.toPowerSeries i) s ∈ J :=
    fun i => nilEval_mem J n _ (h.constantCoeff_eq_zero i) s hs
  have hht : ∀ i, MvFormalGroup.nilEval n (h.toPowerSeries i) t ∈ J :=
    fun i => nilEval_mem J n _ (h.constantCoeff_eq_zero i) t ht

  have e1 : (x + y).val = F.nilMul n s t := by
    funext j
    rw [MvFormalGroup.Points.val_add]
    exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ hst).symm
  have lhs : (h.evalPoints (x + y)).val = fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) (F.nilMul n s t) := by
    funext i
    rw [MvFormalGroup.Hom.val_evalPoints, e1]
    exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ hFst).symm
  have ex : (h.evalPoints x).val = fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) s := by
    funext i
    rw [MvFormalGroup.Hom.val_evalPoints]
    exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ hs).symm
  have ey : (h.evalPoints y).val = fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) t := by
    funext i
    rw [MvFormalGroup.Hom.val_evalPoints]
    exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ ht).symm
  have rhs : (h.evalPoints x + h.evalPoints y).val =
      G.nilMul n (fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) s)
        (fun i => MvFormalGroup.nilEval n (h.toPowerSeries i) t) := by
    funext i
    rw [MvFormalGroup.Points.val_add, ex, ey]
    exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ (forall_sumElim hhs hht)).symm
  rw [lhs, rhs] at key
  exact key

end Nil

section Act

variable {B : Type} [CommRing B] {C : Type} [CommRing C] [Algebra B C] {g : ℕ}

def ap (n : ℕ) (ψ : Fin g → MvPowerSeries (Fin g) B) (x : Fin g → C) : Fin g → C :=
  fun i => MvFormalGroup.nilEval n (ψ i) x

theorem ap_apply (n : ℕ) (ψ : Fin g → MvPowerSeries (Fin g) B) (x : Fin g → C) (i : Fin g) :
    ap n ψ x i = MvFormalGroup.nilEval n (ψ i) x := rfl

variable (J : Ideal C) (n : ℕ)

theorem ap_mem (ψ : Fin g → MvPowerSeries (Fin g) B) (hψ : ∀ i, constantCoeff (ψ i) = 0) (x : Fin g → C)
    (hx : ∀ i, x i ∈ J) (i : Fin g) : ap n ψ x i ∈ J :=
  nilEval_mem J n _ (hψ i) x hx

theorem ap_id (hJ : J ^ (n + 1) = ⊥) (x : Fin g → C) (hx : ∀ i, x i ∈ J) :
    ap n (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin g) B)) x = x :=
  funext fun i => nilEval_X J n hJ x hx i

theorem ap_comp (hJ : J ^ (n + 1) = ⊥) (ψ φ : Fin g → MvPowerSeries (Fin g) B) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (x : Fin g → C) (hx : ∀ i, x i ∈ J) : ap n (fun i => subst φ (ψ i)) x = ap n ψ (ap n φ x) :=
  funext fun i => nilEval_subst J n hJ φ hφ (ψ i) x hx

theorem ap_natural {C' : Type} [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C') (ψ : Fin g → MvPowerSeries (Fin g) B)
    (x : Fin g → C) : φ ∘ ap n ψ x = ap n ψ (φ ∘ x) :=
  funext fun i => nilEval_natural φ n (ψ i) x

end Act

section Transport

variable {B : Type} [CommRing B] {g : ℕ}

def ev (ψ : Fin g → MvPowerSeries (Fin g) B) (C : Type) [CommRing C] [Algebra B C] (t : Fin g → C) : Fin g → C :=
  fun i => MvFormalGroup.adicEval (Ideal.span (Set.range t)) t (ψ i)

theorem ev_eq_ap (ψ : Fin g → MvPowerSeries (Fin g) B) {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ)
    (hJ : J ^ (n + 1) = ⊥) (t : Fin g → C) (ht : ∀ i, t i ∈ J) : ev ψ C t = ap n ψ t := by
  funext i
  have hle : Ideal.span (Set.range t) ≤ J := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht i)
  have h0 : (Ideal.span (Set.range t)) ^ (n + 1) = ⊥ := pow_succ_eq_bot_of_le hJ hle
  have ht0 : ∀ i, t i ∈ Ideal.span (Set.range t) := fun i => Ideal.subset_span ⟨i, rfl⟩
  exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot _ n h0 (ψ i) t ht0).symm

variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

def transport (θ : RelativeGroupLaw.FormalCoordinates f g) (ψ : Fin g → MvPowerSeries (Fin g) B) :
    RelativeGroupLaw.FormalCoordinates f g :=
  fun C _ _ t => θ C (ev ψ C t)

theorem transport_apply (θ : RelativeGroupLaw.FormalCoordinates f g) (ψ : Fin g → MvPowerSeries (Fin g) B)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (t : Fin g → C) (ht : ∀ i, t i ∈ J) : transport θ ψ C t = θ C (ap n ψ t) := by
  show θ C (ev ψ C t) = θ C (ap n ψ t)
  rw [ev_eq_ap ψ J n hJ t ht]

theorem ap_ap_of_hom_comp_eq_id {F F' : MvFormalGroup g B}
    (u : MvFormalGroup.Hom F F') (w : MvFormalGroup.Hom F' F) (hwu : w.comp u = MvFormalGroup.Hom.id F)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : Fin g → C) (hs : ∀ i, s i ∈ J) :
    ap n w.toPowerSeries (ap n u.toPowerSeries s) = s := by
  have h := congrArg MvFormalGroup.Hom.toPowerSeries hwu
  rw [← ap_comp J n hJ _ _ u.constantCoeff_eq_zero s hs]
  change ap n (w.comp u).toPowerSeries s = s
  rw [h]
  exact ap_id J n hJ s hs

theorem isFormalCoordinates_transport_hom (L : RelativeGroupLaw B f) {F F' : MvFormalGroup g B}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (u : MvFormalGroup.Hom F F') (w : MvFormalGroup.Hom F' F)
    (hwu : w.comp u = MvFormalGroup.Hom.id F) (huw : u.comp w = MvFormalGroup.Hom.id F') :
    L.IsFormalCoordinates F' (transport θ w.toPowerSeries) := by
  have hw0 : ∀ i, constantCoeff (w.toPowerSeries i) = 0 := w.constantCoeff_eq_zero
  have hu0 : ∀ i, constantCoeff (u.toPowerSeries i) = 0 := u.constantCoeff_eq_zero
  refine ⟨?_, fun C _ _ J n hJ => ?_⟩
  · intro C _ _ C' _ _ φ s hs
    obtain ⟨n, hn⟩ := exists_span_range_pow_succ_eq_bot s hs
    set J : Ideal C := Ideal.span (Set.range s) with hJdef
    have hsJ : ∀ i, s i ∈ J := fun i => Ideal.subset_span ⟨i, rfl⟩
    set J' : Ideal C' := J.map φ.toRingHom with hJ'def
    have hn' : J' ^ (n + 1) = ⊥ := by rw [hJ'def, ← Ideal.map_pow, hn, Ideal.map_bot]
    have hsJ' : ∀ i, (φ ∘ s) i ∈ J' := fun i => Ideal.mem_map_of_mem _ (hsJ i)
    have hws : ∀ i, ap n w.toPowerSeries s i ∈ J := ap_mem J n _ hw0 s hsJ
    rw [transport_apply θ w.toPowerSeries J' n hn' (φ ∘ s) hsJ', transport_apply θ w.toPowerSeries J n hn s hsJ,
      ← ap_natural n φ w.toPowerSeries s]
    exact hθ.1 C C' φ (ap n w.toPowerSeries s) fun i => isNilpotent_of_mem hn (hws i)
  · obtain ⟨hinto, hinj, honto, hhom⟩ := hθ.2 C J n hJ
    have hwmem : ∀ t : Fin g → C, (∀ i, t i ∈ J) → ∀ i, ap n w.toPowerSeries t i ∈ J :=
      fun t ht => ap_mem J n _ hw0 t ht
    have humem : ∀ t : Fin g → C, (∀ i, t i ∈ J) → ∀ i, ap n u.toPowerSeries t i ∈ J :=
      fun t ht => ap_mem J n _ hu0 t ht
    refine ⟨fun s hs => ?_, fun s t hs ht hst => ?_, fun P hP => ?_, fun s t hs ht => ?_⟩
    · rw [transport_apply θ w.toPowerSeries J n hJ s hs]
      exact hinto _ (hwmem s hs)
    · rw [transport_apply θ w.toPowerSeries J n hJ s hs, transport_apply θ w.toPowerSeries J n hJ t ht] at hst
      have h := hinj _ _ (hwmem s hs) (hwmem t ht) hst
      rw [← ap_ap_of_hom_comp_eq_id w u huw J n hJ s hs, ← ap_ap_of_hom_comp_eq_id w u huw J n hJ t ht, h]
    · obtain ⟨x, hx, hxP⟩ := honto P hP
      refine ⟨ap n u.toPowerSeries x, humem x hx, ?_⟩
      rw [transport_apply θ w.toPowerSeries J n hJ _ (humem x hx), ap_ap_of_hom_comp_eq_id u w hwu J n hJ x hx]
      exact hxP
    · have hst : ∀ i, F'.nilMul n s t i ∈ J := nilMul_mem F' J n s t hs ht
      rw [transport_apply θ w.toPowerSeries J n hJ _ hst, transport_apply θ w.toPowerSeries J n hJ s hs,
        transport_apply θ w.toPowerSeries J n hJ t ht]
      have hadd := nilEval_hom_nilMul w J n hJ s t hs ht
      change ap n w.toPowerSeries (F'.nilMul n s t) = F.nilMul n (ap n w.toPowerSeries s) (ap n w.toPowerSeries t) at hadd
      rw [hadd]
      exact hhom _ _ (hwmem s hs) (hwmem t ht)

end Transport

end GoodReductionJacobian.RelativeGroupLaw.TransportCoords

end

open GoodReductionJacobian.RelativeGroupLaw.TransportCoords in
theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g : ℕ} (F G : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (Φ : MvFormalGroup.Hom G F) (Ψ : MvFormalGroup.Hom F G)
    (hΨΦ : Ψ.comp Φ = MvFormalGroup.Hom.id G) (hΦΨ : Φ.comp Ψ = MvFormalGroup.Hom.id F) :
    L.IsFormalCoordinates G
        (fun (C : Type) _ _ (s : Fin g → C) =>
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i))) ∧
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin g → C, (∀ i, s i ∈ J) →
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i)) =
            θ C (fun i => MvFormalGroup.nilEval n (Φ.toPowerSeries i) s) := by
  refine ⟨isFormalCoordinates_transport_hom L θ hθ Ψ Φ hΦΨ hΨΦ, ?_⟩
  intro C _ _ J n hJ s hs
  exact transport_apply θ Φ.toPowerSeries J n hJ s hs

end S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom (solution)
