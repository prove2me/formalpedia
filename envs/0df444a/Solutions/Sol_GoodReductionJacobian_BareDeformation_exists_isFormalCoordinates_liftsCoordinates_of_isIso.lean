-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ac8c58dd-763d-59f6-ba1e-15a51e8ee315

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso.CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso.CerednikDrinfeld.QM.FakeEllipticCurve"

open scoped Quaternion
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff constantCoeff_subst_eq_zero)

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "A f L C"
namespace TransportAlongIso
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

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

variable {B : Type} [CommRing B] {C : Type} [CommRing C] [Algebra B C]

def ap (n : ℕ) (ψ : Series B) (x : Fin 2 → C) : Fin 2 → C := fun i => MvFormalGroup.nilEval n (ψ i) x

theorem ap_apply (n : ℕ) (ψ : Series B) (x : Fin 2 → C) (i : Fin 2) :
    ap n ψ x i = MvFormalGroup.nilEval n (ψ i) x := rfl

variable (J : Ideal C) (n : ℕ)

theorem ap_mem (ψ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0) (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) (i : Fin 2) :
    ap n ψ x i ∈ J :=
  nilEval_mem J n _ (hψ i) x hx

theorem ap_id (hJ : J ^ (n + 1) = ⊥) (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) : ap n (Series.id B) x = x :=
  funext fun i => nilEval_X J n hJ x hx i

theorem ap_comp (hJ : J ^ (n + 1) = ⊥) (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) : ap n (ψ.comp φ) x = ap n ψ (ap n φ x) :=
  funext fun i => nilEval_subst J n hJ φ hφ (ψ i) x hx

theorem ap_addVia (hJ : J ^ (n + 1) = ⊥) (F : MvFormalGroup 2 B) (φ ψ : Series B)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) : ap n (Series.addVia F φ ψ) x = F.nilMul n (ap n φ x) (ap n ψ x) := by
  funext i
  show MvFormalGroup.nilEval n (subst (Sum.elim φ ψ) (F.toPowerSeries i)) x =
    MvFormalGroup.nilEval n (F.toPowerSeries i) (Sum.elim (ap n φ x) (ap n ψ x))
  have h0 : ∀ c, constantCoeff (Sum.elim φ ψ c) = 0 := by
    rintro (j | j)
    exacts [hφ j, hψ j]
  rw [nilEval_subst J n hJ (Sum.elim φ ψ) h0 (F.toPowerSeries i) x hx]
  congr 1
  funext c
  rcases c with j | j <;> rfl

theorem ap_natural {C' : Type} [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C') (ψ : Series B) (x : Fin 2 → C) :
    φ ∘ ap n ψ x = ap n ψ (φ ∘ x) :=
  funext fun i => nilEval_natural φ n (ψ i) x

end Act

section Transport

variable {B : Type} [CommRing B]

def ev (ψ : Series B) (C : Type) [CommRing C] [Algebra B C] (t : Fin 2 → C) : Fin 2 → C :=
  fun i => MvFormalGroup.adicEval (Ideal.span (Set.range t)) t (ψ i)

theorem ev_eq_ap (ψ : Series B) {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (t : Fin 2 → C) (ht : ∀ i, t i ∈ J) : ev ψ C t = ap n ψ t := by
  funext i
  have hle : Ideal.span (Set.range t) ≤ J := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht i)
  have h0 : (Ideal.span (Set.range t)) ^ (n + 1) = ⊥ := pow_succ_eq_bot_of_le hJ hle
  have ht0 : ∀ i, t i ∈ Ideal.span (Set.range t) := fun i => Ideal.subset_span ⟨i, rfl⟩
  exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot _ n h0 (ψ i) t ht0).symm

variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

def transport (θ : RelativeGroupLaw.FormalCoordinates f 2) (g : Series B) : RelativeGroupLaw.FormalCoordinates f 2 :=
  fun C _ _ t => θ C (ev g C t)

theorem transport_apply (θ : RelativeGroupLaw.FormalCoordinates f 2) (g : Series B)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (t : Fin 2 → C) (ht : ∀ i, t i ∈ J) : transport θ g C t = θ C (ap n g t) := by
  show θ C (ev g C t) = θ C (ap n g t)
  rw [ev_eq_ap g J n hJ t ht]

theorem ap_ap_of_hom_comp_eq_id {F F' : MvFormalGroup 2 B}
    (u : MvFormalGroup.Hom F F') (g : MvFormalGroup.Hom F' F) (hgu : g.comp u = MvFormalGroup.Hom.id F)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : Fin 2 → C) (hs : ∀ i, s i ∈ J) :
    ap n g.toPowerSeries (ap n u.toPowerSeries s) = s := by
  have h := congrArg MvFormalGroup.Hom.toPowerSeries hgu
  rw [← ap_comp J n hJ _ _ u.constantCoeff_eq_zero s hs]
  change ap n (g.comp u).toPowerSeries s = s
  rw [h]
  exact ap_id J n hJ s hs

theorem isFormalCoordinates_transport_hom (L : RelativeGroupLaw B f) {F F' : MvFormalGroup 2 B}
    (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (u : MvFormalGroup.Hom F F') (g : MvFormalGroup.Hom F' F)
    (hgu : g.comp u = MvFormalGroup.Hom.id F) (hug : u.comp g = MvFormalGroup.Hom.id F') :
    L.IsFormalCoordinates F' (transport θ g.toPowerSeries) := by
  have hg0 : ∀ i, constantCoeff (g.toPowerSeries i) = 0 := g.constantCoeff_eq_zero
  have hu0 : ∀ i, constantCoeff (u.toPowerSeries i) = 0 := u.constantCoeff_eq_zero
  refine ⟨?_, fun C _ _ J n hJ => ?_⟩
  · intro C _ _ C' _ _ φ s hs
    obtain ⟨n, hn⟩ := exists_span_range_pow_succ_eq_bot s hs
    set J : Ideal C := Ideal.span (Set.range s) with hJdef
    have hsJ : ∀ i, s i ∈ J := fun i => Ideal.subset_span ⟨i, rfl⟩
    set J' : Ideal C' := J.map φ.toRingHom with hJ'def
    have hn' : J' ^ (n + 1) = ⊥ := by rw [hJ'def, ← Ideal.map_pow, hn, Ideal.map_bot]
    have hsJ' : ∀ i, (φ ∘ s) i ∈ J' := fun i => Ideal.mem_map_of_mem _ (hsJ i)
    have hgs : ∀ i, ap n g.toPowerSeries s i ∈ J := ap_mem J n _ hg0 s hsJ
    rw [transport_apply θ g.toPowerSeries J' n hn' (φ ∘ s) hsJ', transport_apply θ g.toPowerSeries J n hn s hsJ,
      ← ap_natural n φ g.toPowerSeries s]
    exact hθ.1 C C' φ (ap n g.toPowerSeries s) fun i => isNilpotent_of_mem hn (hgs i)
  · obtain ⟨hinto, hinj, honto, hhom⟩ := hθ.2 C J n hJ
    have hgmem : ∀ t : Fin 2 → C, (∀ i, t i ∈ J) → ∀ i, ap n g.toPowerSeries t i ∈ J :=
      fun t ht => ap_mem J n _ hg0 t ht
    have humem : ∀ t : Fin 2 → C, (∀ i, t i ∈ J) → ∀ i, ap n u.toPowerSeries t i ∈ J :=
      fun t ht => ap_mem J n _ hu0 t ht
    refine ⟨fun s hs => ?_, fun s t hs ht hst => ?_, fun P hP => ?_, fun s t hs ht => ?_⟩
    · rw [transport_apply θ g.toPowerSeries J n hJ s hs]
      exact hinto _ (hgmem s hs)
    · rw [transport_apply θ g.toPowerSeries J n hJ s hs, transport_apply θ g.toPowerSeries J n hJ t ht] at hst
      have h := hinj _ _ (hgmem s hs) (hgmem t ht) hst
      rw [← ap_ap_of_hom_comp_eq_id g u hug J n hJ s hs, ← ap_ap_of_hom_comp_eq_id g u hug J n hJ t ht, h]
    · obtain ⟨x, hx, hxP⟩ := honto P hP
      refine ⟨ap n u.toPowerSeries x, humem x hx, ?_⟩
      rw [transport_apply θ g.toPowerSeries J n hJ _ (humem x hx), ap_ap_of_hom_comp_eq_id u g hgu J n hJ x hx]
      exact hxP
    · have hst : ∀ i, F'.nilMul n s t i ∈ J := nilMul_mem F' J n s t hs ht
      rw [transport_apply θ g.toPowerSeries J n hJ _ hst, transport_apply θ g.toPowerSeries J n hJ s hs,
        transport_apply θ g.toPowerSeries J n hJ t ht]
      have hadd := nilEval_hom_nilMul g J n hJ s t hs ht
      change ap n g.toPowerSeries (F'.nilMul n s t) = F.nilMul n (ap n g.toPowerSeries s) (ap n g.toPowerSeries t) at hadd
      rw [hadd]
      exact hhom _ _ (hgmem s hs) (hgmem t ht)

theorem nilEval_eq_nilEval_map {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    {C : Type} [CommRing C] [Algebra B C] [Algebra B₁ C] [IsScalarTower B B₁ C]
    (n : ℕ) (p : MvPowerSeries (Fin 2) B) (s : Fin 2 → C) :
    MvFormalGroup.nilEval n p s = MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap B B₁) p) s := by
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  have htr : MvPowerSeries.trunc' B₁ (Finsupp.equivFunOnFinite.symm fun _ => n) (MvPowerSeries.map (algebraMap B B₁) p) =
      MvPolynomial.map (algebraMap B B₁) (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) p) := by
    ext m
    rw [MvPowerSeries.coeff_trunc', MvPolynomial.coeff_map, MvPowerSeries.coeff_trunc']
    split_ifs <;> simp
  rw [htr, MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]

end Transport

end CerednikDrinfeld.QM.FakeEllipticCurve.TransportAlongIso

end

open CerednikDrinfeld.QM.FakeEllipticCurve.TransportAlongIso in
theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2)
    (D : BareDeformation f₁ L₁ B) (G G' : MvFormalGroup.Deformation Ĝ₁ B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hl : D.LiftsCoordinates θ₁ θ) (hiso : G.IsIso G') :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates D.f 2, D.L.IsFormalCoordinates G'.F θ' ∧ D.LiftsCoordinates θ₁ θ' := by
  classical
  obtain ⟨φ, ⟨ψ, hψφ, hφψ⟩, hφX⟩ := hiso
  refine ⟨transport θ ψ.toPowerSeries, isFormalCoordinates_transport_hom D.L θ hθ φ ψ hψφ hφψ, ?_⟩
  intro B'' _ _ _ _ s hs
  obtain ⟨n, hn⟩ := exists_span_range_pow_succ_eq_bot s hs
  have hsJ : ∀ i, s i ∈ Ideal.span (Set.range s) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hφs : ap n φ.toPowerSeries s = s := by
    funext i
    rw [ap_apply, nilEval_eq_nilEval_map (B₁ := B₁) n (φ.toPowerSeries i) s, hφX i]
    exact nilEval_X (Ideal.span (Set.range s)) n hn s hsJ i
  have hψs : ap n ψ.toPowerSeries s = s := by
    conv_lhs => rw [← hφs]
    exact ap_ap_of_hom_comp_eq_id φ ψ hψφ (Ideal.span (Set.range s)) n hn s hsJ
  change (θ₁ B'' s).1 ≫ D.g = (transport θ ψ.toPowerSeries B'' s).1
  rw [transport_apply θ ψ.toPowerSeries (Ideal.span (Set.range s)) n hn s hsJ, hψs]
  exact hl B'' s hs

end S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso (solution)
