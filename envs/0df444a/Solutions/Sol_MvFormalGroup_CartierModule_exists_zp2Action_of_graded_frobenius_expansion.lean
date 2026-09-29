-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b2828d92-b62c-5c27-869f-9434fa158a4b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Theorems.Thm_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
import Definitions.Def_MvFormalGroup_WittPointFamily
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

universe u v

namespace ActOnLawAux

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

theorem witt_map_frobenius {R : Type u} {S : Type v} [CommRing R] [CommRing S] (g : R →+* S)
    (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.map_aeval,
    funext (WittVector.map_coeff g _)]
  rw [RingHom.ext_int ((g : R →+* S).comp (algebraMap ℤ R)) (algebraMap ℤ S), MvPolynomial.aeval_eq_eval₂Hom]

theorem ghostComponent_eq_of_coeff_eq {R : Type u} [CommRing R] (n : ℕ) (x y : WittVector p R)
    (h : ∀ i ≤ n, x.coeff i = y.coeff i) :
    WittVector.ghostComponent n x = WittVector.ghostComponent n y := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem eq_of_forall_ghostComponent_eq {R : Type u} [CommRing R] (hpnz : (p : R) ∈ nonZeroDivisors R)
    (x y : WittVector p R) (h : ∀ k, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    x = y := by
  ext k
  exact WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) x y
    (fun i _ => h i) k (Nat.lt_succ_self k)

theorem eq_teichmuller_add_verschiebung_shift {R : Type u} [CommRing R] (w : WittVector p R) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

theorem frobenius_sub_pow_mem {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (a : WittVector p k) :
    WittVector.frobenius a - a ^ p ∈ Ideal.span {(p : WittVector p k)} := by

  set y := a.shift 1
  obtain ⟨z, hz⟩ : ∃ z : WittVector p k, WittVector.frobenius z = y :=
    ⟨(WittVector.frobeniusEquiv p k).symm y, (WittVector.frobeniusEquiv p k).apply_symm_apply y⟩
  have hV : WittVector.verschiebung y = z * p := by rw [← hz, WittVector.verschiebung_frobenius]
  have ha : a = WittVector.teichmuller p (a.coeff 0) + z * p := by
    rw [← hV]; exact eq_teichmuller_add_verschiebung_shift p a
  have hmem : a - WittVector.teichmuller p (a.coeff 0) ∈ Ideal.span {(p : WittVector p k)} := by
    nth_rw 1 [ha]
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hF : WittVector.frobenius a - WittVector.teichmuller p (a.coeff 0) ^ p
      ∈ Ideal.span {(p : WittVector p k)} := by
    have : WittVector.frobenius (WittVector.teichmuller p (a.coeff 0))
        = WittVector.teichmuller p (a.coeff 0) ^ p := by
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
        ← map_pow]
    rw [← this, ← map_sub]
    nth_rw 1 [ha]
    rw [add_sub_cancel_left, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hP : a ^ p - WittVector.teichmuller p (a.coeff 0) ^ p ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_pow, map_pow]
    have h0 : Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) a =
        Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) (WittVector.teichmuller p (a.coeff 0)) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
    rw [h0]
  have := Ideal.sub_mem _ hF hP
  rwa [sub_sub_sub_cancel_right] at this

theorem frobenius_teichmuller {k : Type u} [CommRing k] [CharP k p] (c : k) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p c ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← map_pow]

theorem frobenius_iterate_teichmuller {k : Type u} [CommRing k] [CharP k p] (c : k) (n : ℕ) :
    (⇑(WittVector.frobenius (p := p) (R := k)))^[n] (WittVector.teichmuller p c)
      = WittVector.teichmuller p c ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_pow, frobenius_teichmuller, ← pow_mul,
      pow_succ, mul_comm]

theorem frobenius_frobenius_zp2 (a : CerednikDrinfeld.Zp2 p) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  rw [← sq, ← hcard, FiniteField.pow_card]

theorem p_mem_nonZeroDivisors_zp2 :
    (p : CerednikDrinfeld.Zp2 p) ∈ nonZeroDivisors (CerednikDrinfeld.Zp2 p) := by
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => CerednikDrinfeld.CartierLift.zp2_natCast_mul_eq_zero (p := p) x hx,
    fun x hx => CerednikDrinfeld.CartierLift.zp2_natCast_mul_eq_zero (p := p) x (by rwa [mul_comm] at hx)⟩

end Witt

end ActOnLawAux

noncomputable section

namespace P2mLawPresWx

open MvPowerSeries

section Generic

open MvFormalGroup

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem hasSubst_constX (i : Fin d) :
    HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X i

def linMap (Φ : MvFormalGroup d R) [Φ.IsComm] (m : ℕ) :
    SeriesPoint Φ (Fin m) →+ Matrix (Fin d) (Fin m) R where
  toFun a := linearPart a.val
  map_zero' := by rw [SeriesPoint.val_zero]; exact linearPart_zero
  map_add' a b := by
    rw [SeriesPoint.val_add]
    exact linearPart_subst_elim Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero

@[scoped simp] theorem linMap_apply [Φ.IsComm] (m : ℕ) (a : SeriesPoint Φ (Fin m)) :
    linMap Φ m a = linearPart a.val :=
  rfl

def XPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d) := ⟨fun i => X i, fun i => constantCoeff_X i⟩

def inlPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inl l), fun _ => constantCoeff_X _⟩

def inrPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inr l), fun _ => constantCoeff_X _⟩

theorem val_inlPt_add_inrPt : (inlPt Φ + inrPt Φ).val = Φ.toPowerSeries := by
  rw [SeriesPoint.val_add]
  funext j
  have hX : Sum.elim (inlPt Φ).val (inrPt Φ).val =
      fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) R) := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX]
  exact congrFun subst_self _

theorem prod_X_pow_eq_monomial {σ : Type*} (e : σ →₀ ℕ) :
    (e.prod fun s k => (X s : MvPowerSeries σ R) ^ k) = monomial e 1 := by
  have h := monomial_eq e (fun _ : σ => (1 : R))
  have h1 : (e.prod fun _ n => (1 : R) ^ n) = 1 := by simp [Finsupp.prod]
  rw [h1] at h
  rw [h]
  exact Finsupp.prod_congr fun s _ => by rw [one_smul]

end Generic

section Section

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

def cwPt (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (d : ℕ) (i : Fin d) :
    WittLaw.seriesPoint p R (Fin d) :=
  WittLaw.substPt (b := fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) (hasSubst_constX i)
    (fun _ => constantCoeff_X i) WittLaw.curveTautPt

theorem val_evalPt_cwPt (g : CartierModule p Φ) (i : Fin d) :
    (evalPt g (cwPt p R d i)).val = fun j => subst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R))
      (curve g j) := by
  rw [cwPt, ← substPt_evalPt]
  rfl

theorem coeff_single_val_evalPt_cwPt (g : CartierModule p Φ) (i j j' : Fin d) :
    coeff (Finsupp.single j' 1) ((evalPt g (cwPt p R d i)).val j) =
      if j' = i then tangent g j else 0 := by
  classical
  rw [val_evalPt_cwPt]
  dsimp only
  rw [coeff_single_subst (fun _ => constantCoeff_X i), Fintype.sum_unique, coeff_X,
    ← PowerSeries.coeff_def (s := Finsupp.single (default : Unit) 1) (n := 1) (by simp), coeff_one_curve]
  by_cases hji : j' = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg (fun h => hji (Finsupp.single_left_injective one_ne_zero h)), if_neg hji, mul_zero]

def GPt (f : Fin d → CartierModule p Φ) : SeriesPoint Φ (Fin d) :=
  presPi f (cwPt p R d)

theorem linearPart_GPt (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0) : linearPart (GPt (p := p) f).val = 1 := by
  rw [← linMap_apply, GPt, presPi_def, map_sum]
  ext j j'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [linMap_apply, linearPart, Matrix.of_apply, coeff_single_val_evalPt_cwPt]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hf]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem presPi_substPt {ι : Type*} [Fintype ι] (F : ι → CartierModule p Φ) {τ : Type v}
    {τ' : Type*} {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ t, (b t).constantCoeff = 0)
    (v : ι → WittLaw.seriesPoint p R τ) :
    presPi F (fun l => WittLaw.substPt hb hb0 (v l)) = SeriesPoint.substPt hb hb0 (presPi F v) := by
  simp only [presPi_def, map_sum, substPt_evalPt]

variable (f : Fin d → CartierModule p Φ) {uinv : Fin d → MvPowerSeries (Fin d) R}
  (hu0 : ∀ i, (uinv i).constantCoeff = 0) (hu : ∀ i, subst uinv ((GPt (p := p) f).val i) = X i)

def wX : Fin d → WittLaw.seriesPoint p R (Fin d) := fun l =>
  WittLaw.substPt (hasSubst_of_constantCoeff_zero hu0) hu0 (cwPt p R d l)

include hu in

theorem presPi_wX : presPi f (wX (p := p) hu0) = XPt Φ := by
  unfold wX
  rw [presPi_substPt]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact hu i

def wOf {τ : Type v} (a : SeriesPoint Φ τ) : Fin d → WittLaw.seriesPoint p R τ := fun l =>
  WittLaw.substPt a.hasSubst_val a.constantCoeff_eq_zero (wX (p := p) hu0 l)

include hu in

theorem presPi_wOf {τ : Type v} (a : SeriesPoint Φ τ) : presPi f (wOf (p := p) hu0 a) = a := by
  unfold wOf
  rw [presPi_substPt, presPi_wX f hu0 hu]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact subst_X a.hasSubst_val i

end Section

section HomEq

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d' R} [Φ.IsComm] [Ψ.IsComm]

theorem hom_eq_of_map_basis_eq (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    (φ ψ : Φ.Hom Ψ) (h : ∀ l, CartierModule.map φ (f l) = CartierModule.map ψ (f l)) : φ = ψ := by
  obtain ⟨uinv, hu0, -, hu⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
    (GPt (p := p) f).val (GPt (p := p) f).constantCoeff_eq_zero (linearPart_GPt f hf)
  have key : SeriesPoint.mapPt φ (XPt Φ) = SeriesPoint.mapPt ψ (XPt Φ) := by
    rw [← presPi_wX (p := p) f hu0 hu, mapPt_presPi, mapPt_presPi]
    congr 1
    funext l
    exact h l
  apply MvFormalGroup.Hom.ext
  funext j
  have hv := congrArg (fun a : SeriesPoint Ψ (Fin d) => a.val j) key
  simp only [SeriesPoint.val_mapPt, XPt] at hv
  have hX : (fun i => (X i : MvPowerSeries (Fin d) R)) = MvPowerSeries.X := rfl
  rw [hX, MvPowerSeries.subst_self] at hv
  exact hv

end HomEq

end P2mLawPresWx
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.P2mLawPresWx"

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.P2mLawPresWx"

namespace ActOnLawAux

open MvFormalGroup MvFormalGroup.CartierModule

section Cartier

variable (p : ℕ) [hp : Fact p.Prime] {B : Type u} [CommRing B]
  {Φ : MvFormalGroup 2 B} [Φ.IsComm] {Ψ : MvFormalGroup 2 B} [Ψ.IsComm]

theorem iterate_verschiebungInt_map (ψ : Φ.Hom Ψ) (m : ℕ) (x : CartierModule p Φ) :
    (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m] (map ψ x) =
      map ψ ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_verschiebungInt]

theorem expansion_map (ψ : Φ.Hom Ψ)
    (f : Fin 2 → CartierModule p Φ) (c : ℕ → Fin 2 → Fin 2 → B) (h : ℕ → Fin 2 → CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, homothety (c m i l) (f l))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i)) :
    ∀ (i : Fin 2) (N : ℕ), ∃ h' : CartierModule p Ψ,
      frobenius (map ψ (f i)) =
        (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[(m : ℕ)]
          (∑ k : Fin 2, homothety (c m i k) (map ψ (f k)))) +
        (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] h' := by
  intro i N
  refine ⟨map ψ (h N i), ?_⟩
  rw [← CartierModule.map_frobenius, hexp N i, map_add, map_sum, ← iterate_verschiebungInt_map,
    ← Finset.sum_range (fun m => (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m]
      (∑ k : Fin 2, homothety (c m i k) (map ψ (f k))))]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← iterate_verschiebungInt_map, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_homothety]

variable [Algebra (PadicInt p) B]

theorem hom_eq (ψ₁ ψ₂ : Φ.Hom Φ)
    (f : Fin 2 → CartierModule p Φ)
    (hf : ∀ i l, tangent (f i) l = if i = l then 1 else 0)
    (c : ℕ → Fin 2 → Fin 2 → B) (h : ℕ → Fin 2 → CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, homothety (c m i l) (f l))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (heq : ∀ i, map ψ₁ (f i) = map ψ₂ (f i)) : ψ₁ = ψ₂ :=
  P2mLawPresWx.hom_eq_of_map_basis_eq (p := p) f hf ψ₁ ψ₂ heq

end Cartier
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.P2mLawPresWx"

end ActOnLawAux
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.P2mLawPresWx"

open ActOnLawAux MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i l, MvFormalGroup.CartierModule.tangent (f i) l = if i = l then 1 else 0)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i)) :
    ∃ (θ : CerednikDrinfeld.Zp2 p →+* WittVector p (CerednikDrinfeld.Zp2 p))
      (act : CerednikDrinfeld.Zp2 p → CerednikDrinfeld.SpecialFormal.Series B)
      (hact : ∀ a, CerednikDrinfeld.SpecialFormal.IsLawHom Φ Φ (act a)),
      (∀ (a : CerednikDrinfeld.Zp2 p) (n : ℕ), WittVector.ghostComponent n (θ a) =
          (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] a) ∧
      (∀ c : GaloisField p 2, θ (WittVector.teichmuller p c) =
          WittVector.teichmuller p (WittVector.teichmuller p c)) ∧
      act 1 = CerednikDrinfeld.SpecialFormal.Series.id B ∧
      (∀ a b, act (a * b) = (act a).comp (act b)) ∧
      (∀ a b, act (a + b) = CerednikDrinfeld.SpecialFormal.Series.addVia Φ (act a) (act b)) ∧
      ∀ (a : CerednikDrinfeld.Zp2 p) (i : Fin 2),
        MvFormalGroup.CartierModule.map (hact a).toHom (f i) =
          WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a)) • f i := by
  classical
  have hpnz := p_mem_nonZeroDivisors_zp2 p
  obtain ⟨θ, hθ⟩ := WittVector.exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift p hpnz
    (WittVector.frobenius (p := p) (R := GaloisField p 2)) (frobenius_sub_pow_mem p)

  have hθσ : ∀ a, WittVector.frobenius (θ a) = θ (WittVector.frobenius a) := by
    intro a
    apply eq_of_forall_ghostComponent_eq p hpnz
    intro k
    rw [WittVector.ghostComponent_frobenius, hθ, hθ, Function.iterate_succ_apply]

  have hθteich : ∀ c : GaloisField p 2, θ (WittVector.teichmuller p c) =
      WittVector.teichmuller p (WittVector.teichmuller p c) := by
    intro c
    apply eq_of_forall_ghostComponent_eq p hpnz
    intro k
    rw [hθ, WittVector.ghostComponent_teichmuller, frobenius_iterate_teichmuller]
  have hσpow : ∀ (n : ℕ) (x : Zp2 p),
      (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] x =
        ((WittVector.frobenius (p := p) (R := GaloisField p 2)) ^ n) x :=
    fun n x => by rw [RingHom.coe_pow]

  set w : Zp2 p → Fin 2 → WittVector p B := fun a i =>
    WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a)) with hwdef
  have hw : ∀ (a : Zp2 p) (i : Fin 2), WittVector.frobenius (w a i) = w a (i + 1) := by
    intro a i
    simp only [hwdef]
    rw [← witt_map_frobenius, hθσ, ← Function.iterate_succ_apply'
      (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))]
    fin_cases i
    · rfl
    · show WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[2] a)) =
        WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[0] a))
      rw [Function.iterate_zero_apply, Function.iterate_succ_apply', Function.iterate_one,
        frobenius_frobenius_zp2]

  have hexpw := fun a => MvFormalGroup.CartierModule.frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
    p Φ f c hc h hexp (w a) (hw a)
  have hex : ∀ a : Zp2 p, ∃ φ : Φ.Hom Φ, ∀ l, map φ (f l) = w a l • f l := fun a =>
    MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
      p Φ Φ f hf c h hexp (fun l => w a l • f l)
      (fun N i => (⇑(WittVector.frobenius (p := p) (R := B)))^[N + 1] (w a i) • h N i) (hexpw a)
  choose φ hφ using hex
  have hw_one : ∀ i : Fin 2, w 1 i = 1 := by
    intro i; simp only [hwdef]
    rw [Function.iterate_fixed (map_one _) i, map_one, map_one]
  have hw_mul : ∀ (a b : Zp2 p) (i : Fin 2), w (a * b) i = w a i * w b i := by
    intro a b i; simp only [hwdef, hσpow, map_mul]
  have hw_add : ∀ (a b : Zp2 p) (i : Fin 2), w (a + b) i = w a i + w b i := by
    intro a b i; simp only [hwdef, hσpow, map_add]
  refine ⟨θ, fun a => (φ a).toPowerSeries, fun a => IsLawHom.of_hom (φ a), hθ, hθteich,
    ?_, ?_, ?_, ?_⟩
  · have e : φ 1 = MvFormalGroup.Hom.id Φ := hom_eq p (φ 1) (MvFormalGroup.Hom.id Φ) f hf c h hexp
      (fun i => by rw [hφ, map_id, hw_one, one_smul])
    show (φ 1).toPowerSeries = Series.id B
    rw [e]; rfl
  · intro a b
    have e : φ (a * b) = (φ a).comp (φ b) := hom_eq p (φ (a * b)) ((φ a).comp (φ b)) f hf c h hexp
      (fun i => by rw [hφ, map_comp, hφ, map_smul_witt, hφ, smul_smul, hw_mul, mul_comm])
    show (φ (a * b)).toPowerSeries = Series.comp (φ a).toPowerSeries (φ b).toPowerSeries
    rw [e]; rfl
  · intro a b
    have e : φ (a + b) = φ a + φ b := hom_eq p (φ (a + b)) (φ a + φ b) f hf c h hexp
      (fun i => by rw [hφ, map_add_hom, hφ, hφ, ← add_smul, hw_add])
    show (φ (a + b)).toPowerSeries = Series.addVia Φ (φ a).toPowerSeries (φ b).toPowerSeries
    rw [e]; rfl
  · intro a i
    exact hφ a i

end S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion (solution)
