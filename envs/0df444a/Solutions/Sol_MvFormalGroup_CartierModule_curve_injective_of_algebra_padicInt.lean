-- Prove2me | solution 1 for MvFormalGroup.CartierModule.curve_injective_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/00190882-c32f-58e6-9fe2-a56fe324c6f9

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u v

open MvPowerSeries MvFormalGroup MvFormalGroup.WittLaw

namespace CurveInjSol

variable {p : ℕ} [hp : Fact p.Prime]

section Helpers

variable {S : Type v} [CommRing S] {τ : Type*}

def pairOf (a b : ℕ → MvPowerSeries τ S) : Fin 2 × ℕ → MvPowerSeries τ S :=
  fun im => Fin.cases (a im.2) (fun _ => b im.2) im.1

omit hp in
@[scoped simp] theorem pairOf_zero (a b : ℕ → MvPowerSeries τ S) (m : ℕ) : pairOf a b (0, m) = a m := rfl

omit hp in
@[scoped simp] theorem pairOf_one (a b : ℕ → MvPowerSeries τ S) (m : ℕ) : pairOf a b (1, m) = b m := rfl

omit hp in
theorem hasSubst_pairOf {a b : ℕ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (pairOf a b) :=
  WittLaw.hasSubst_finCases ha hb

omit hp in
theorem uncurry_vecCons_eq_pairOf (a b : ℕ → MvPowerSeries τ S) :
    Function.uncurry ![a, b] = pairOf a b := by
  funext ⟨i, m⟩
  fin_cases i <;> rfl

omit hp in

theorem coeff_coePoly (e : Unit →₀ ℕ) (φ : Polynomial S) :
    MvPowerSeries.coeff e (φ : PowerSeries S) = φ.coeff (e ()) := by
  rw [show MvPowerSeries.coeff e (φ : PowerSeries S) = PowerSeries.coeff (e ()) (φ : PowerSeries S)
    from by rw [PowerSeries.coeff_def (s := e) rfl], Polynomial.coeff_coe]

omit hp in
theorem constantCoeff_coePoly (φ : Polynomial S) :
    MvPowerSeries.constantCoeff (φ : PowerSeries S) = φ.coeff 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coePoly]
  rfl

end Helpers

section Points

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} {τ : Type*}

theorem subst_pair_addFam (f : CartierModule p Φ) {a b : ℕ → MvPowerSeries τ R} (ha : HasSubst a)
    (hb : HasSubst b) (j : Fin d) :
    subst (fun n => subst (pairOf a b) (WittLaw.addFam p R n)) (f.toPowerSeries j) =
      subst (Sum.elim (fun l => subst a (f.toPowerSeries l)) fun l => subst b (f.toPowerSeries l))
        (Φ.toPowerSeries j) := by
  have hf := f.constantCoeff_eq_zero
  have hP : HasSubst (pairOf a b) := hasSubst_pairOf ha hb
  have key := congrArg (subst (pairOf a b)) (f.subst_addFam j)
  rw [subst_comp_subst_apply (hasSubst_addFam p R) hP] at key
  rw [key, subst_subst_elim Φ (CartierModule.constantCoeff_inBlk 0 hf)
    (CartierModule.constantCoeff_inBlk 1 hf) hP]
  congr 1
  funext s
  rcases s with l | l
  · show subst (pairOf a b) (subst (blk 0) (f.toPowerSeries l)) = subst a (f.toPowerSeries l)
    rw [subst_comp_subst_apply (hasSubst_blk 0) hP]
    congr 1
    funext m
    exact subst_X hP ((0 : Fin 2), m)
  · show subst (pairOf a b) (subst (blk 1) (f.toPowerSeries l)) = subst b (f.toPowerSeries l)
    rw [subst_comp_subst_apply (hasSubst_blk 1) hP]
    congr 1
    funext m
    exact subst_X hP ((1 : Fin 2), m)

end Points

section Expansion

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

def teichPolyZ : ℕ → MvPolynomial ℕ ℤ
  | 0 => MvPolynomial.X 0
  | _ + 1 => 0

def shiftPolyZ : ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | m + 1 => MvPolynomial.X (m + 1)

def splitPolyZ : Fin 2 × ℕ → MvPolynomial ℕ ℤ :=
  fun im => Fin.cases (teichPolyZ im.2) (fun _ => shiftPolyZ im.2) im.1

theorem aeval_splitPolyZ_wittAdd (n : ℕ) :
    MvPolynomial.aeval splitPolyZ (WittVector.wittAdd p n) = MvPolynomial.X n := by
  let x : WittVector p (MvPolynomial ℕ ℤ) := WittVector.mk p fun m => MvPolynomial.X m
  have h := congrArg (fun w : WittVector p (MvPolynomial ℕ ℤ) => w.coeff n)
    (WittVector.select_add_select_not (fun i => i = 0) x)
  rw [WittVector.add_coeff] at h
  have hG : Function.uncurry ![(WittVector.select (fun i => i = 0) x).coeff,
      (WittVector.select (fun i => ¬ i = 0) x).coeff] = splitPolyZ := by
    funext ⟨i, m⟩
    fin_cases i
    · show (WittVector.select (fun i => i = 0) x).coeff m = teichPolyZ m
      cases m with
      | zero => simp [WittVector.select, x, teichPolyZ]
      | succ m => simp [WittVector.select, x, teichPolyZ]
    · show (WittVector.select (fun i => ¬ i = 0) x).coeff m = shiftPolyZ m
      cases m with
      | zero => simp [WittVector.select, x, shiftPolyZ]
      | succ m => simp [WittVector.select, x, shiftPolyZ]
  unfold WittVector.peval at h
  rw [hG] at h
  exact h

variable (R) in

def teichX : ℕ → MvPowerSeries ℕ R := fun n =>
  ((MvPolynomial.map (Int.castRingHom R) (teichPolyZ n) : MvPolynomial ℕ R) : MvPowerSeries ℕ R)

variable (R) in

def shiftX : ℕ → MvPowerSeries ℕ R := fun n =>
  ((MvPolynomial.map (Int.castRingHom R) (shiftPolyZ n) : MvPolynomial ℕ R) : MvPowerSeries ℕ R)

omit hp in
@[scoped simp] theorem teichX_zero : teichX R 0 = X 0 := by
  simp [teichX, teichPolyZ, MvPolynomial.coe_X]

omit hp in
@[scoped simp] theorem teichX_succ (m : ℕ) : teichX R (m + 1) = 0 := by
  simp [teichX, teichPolyZ]

omit hp in
@[scoped simp] theorem shiftX_zero : shiftX R 0 = 0 := by
  simp [shiftX, shiftPolyZ]

omit hp in
@[scoped simp] theorem shiftX_succ (m : ℕ) : shiftX R (m + 1) = X (m + 1) := by
  simp [shiftX, shiftPolyZ, MvPolynomial.coe_X]

omit hp in
theorem hasSubst_teichX : HasSubst (teichX R) := by
  refine ⟨fun n => ?_, fun e => ?_⟩
  · cases n with
    | zero => rw [teichX_zero, constantCoeff_X]; exact IsNilpotent.zero
    | succ n => rw [teichX_succ, map_zero]; exact IsNilpotent.zero
  · refine (Set.finite_singleton 0).subset fun n hn => ?_
    cases n with
    | zero => rfl
    | succ n => exact absurd (by simp) hn

omit hp in
theorem hasSubst_shiftX : HasSubst (shiftX R) := by
  classical
  refine ⟨fun n => ?_, fun e => ?_⟩
  · cases n with
    | zero => rw [shiftX_zero, map_zero]; exact IsNilpotent.zero
    | succ n => rw [shiftX_succ, constantCoeff_X]; exact IsNilpotent.zero
  · refine (e.support.finite_toSet).subset fun n hn => ?_
    cases n with
    | zero => exact absurd (by simp) hn
    | succ n =>
      have h : coeff e (X (n + 1) : MvPowerSeries ℕ R) ≠ 0 := by simpa using hn
      rw [coeff_X] at h
      split_ifs at h with he
      · subst he
        simp
      · exact absurd rfl h

theorem subst_pairOf_teichX_shiftX_addFam (n : ℕ) :
    subst (pairOf (teichX R) (shiftX R)) (WittLaw.addFam p R n) = X n := by
  have hpair : pairOf (teichX R) (shiftX R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (splitPolyZ im) : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    fin_cases l
    rfl
  rw [hpair, WittLaw.subst_coe_addFam (R := R) splitPolyZ n, aeval_splitPolyZ_wittAdd,
    MvPolynomial.map_X, MvPolynomial.coe_X]

theorem toPowerSeries_eq_subst_elim [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    f.toPowerSeries j =
      subst (Sum.elim (fun l => subst (teichX R) (f.toPowerSeries l))
        fun l => subst (shiftX R) (f.toPowerSeries l)) (Φ.toPowerSeries j) := by
  rw [← subst_pair_addFam f hasSubst_teichX hasSubst_shiftX j]
  have hfam : (fun n => subst (pairOf (teichX R) (shiftX R)) (WittLaw.addFam p R n)) =
      fun n => (X n : MvPowerSeries ℕ R) := funext subst_pairOf_teichX_shiftX_addFam
  rw [hfam]
  exact (congrFun subst_self _).symm

theorem subst_teichX_eq (f : CartierModule p Φ) (l : Fin d) :
    subst (teichX R) (f.toPowerSeries l) =
      subst (fun _ : Unit => (X 0 : MvPowerSeries ℕ R)) (CartierModule.curve f l) := by
  have hc : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries ℕ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  rw [CartierModule.curve_apply, subst_comp_subst_apply CartierModule.hasSubst_curveFam hc]
  congr 1
  funext n
  cases n with
  | zero =>
    rw [teichX_zero]
    show X 0 = subst (fun _ : Unit => (X 0 : MvPowerSeries ℕ R)) (PowerSeries.X : PowerSeries R)
    rw [PowerSeries.X, subst_X hc]
  | succ m =>
    rw [teichX_succ]
    show (0 : MvPowerSeries ℕ R) = subst (fun _ : Unit => (X 0 : MvPowerSeries ℕ R)) (0 : PowerSeries R)
    rw [← coe_substAlgHom hc, map_zero]

def succEmb : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

theorem subst_shiftX_eq [Φ.IsComm] (f : CartierModule p Φ) (l : Fin d) :
    subst (shiftX R) (f.toPowerSeries l) =
      MvPowerSeries.rename succEmb ((CartierModule.frobenius f).toPowerSeries l) := by
  rw [MvPowerSeries.rename_eq_subst, CartierModule.toPowerSeries_frobenius]
  show _ = subst (X ∘ succEmb) (subst (WittLaw.verFam R) (f.toPowerSeries l))
  rw [subst_comp_subst_apply WittLaw.hasSubst_verFam (HasSubst.X_comp _)]
  congr 1
  funext n
  cases n with
  | zero =>
    rw [shiftX_zero, WittLaw.verFam_zero, ← coe_substAlgHom (HasSubst.X_comp _), map_zero]
  | succ m =>
    rw [shiftX_succ, WittLaw.verFam_succ, subst_X (HasSubst.X_comp _)]
    rfl

theorem toPowerSeries_eq_rename_frobenius [Φ.IsComm] (f : CartierModule p Φ)
    (h : ∀ l, CartierModule.curve f l = 0) (j : Fin d) :
    f.toPowerSeries j =
      MvPowerSeries.rename succEmb ((CartierModule.frobenius f).toPowerSeries j) := by
  rw [toPowerSeries_eq_subst_elim f j]
  have hA : (fun l => subst (teichX R) (f.toPowerSeries l)) = fun _ => (0 : MvPowerSeries ℕ R) := by
    funext l
    have hc : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries ℕ R)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [subst_teichX_eq, h l, ← coe_substAlgHom hc, map_zero]
  have hB : (fun l => subst (shiftX R) (f.toPowerSeries l)) =
      fun l => MvPowerSeries.rename succEmb ((CartierModule.frobenius f).toPowerSeries l) :=
    funext (subst_shiftX_eq f)
  rw [hA, hB]
  refine subst_elim_zero_left Φ (fun l => ?_) j
  rw [← subst_shiftX_eq]
  exact constantCoeff_subst_eq_zero hasSubst_shiftX
    (fun n => by cases n <;> simp) (f.constantCoeff_eq_zero l)

theorem eq_zero_of_forall_curve_frobenius_iterate [Φ.IsComm] (f : CartierModule p Φ)
    (h : ∀ n l, CartierModule.curve ((⇑(CartierModule.frobenius (p := p) (Φ := Φ)))^[n] f) l = 0) :
    f = 0 := by
  classical

  have main : ∀ n : ℕ, ∀ g : CartierModule p Φ,
      (∀ k l, CartierModule.curve ((⇑(CartierModule.frobenius (p := p) (Φ := Φ)))^[k] g) l = 0) →
      ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∃ i ∈ e.support, i < n) → coeff e (g.toPowerSeries j) = 0 := by
    intro n
    induction n with
    | zero =>
      rintro g - j e ⟨i, -, hi⟩
      exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      rintro g hg j e ⟨i, hi, hin⟩
      have h0 : ∀ l, CartierModule.curve g l = 0 := fun l => hg 0 l
      rw [toPowerSeries_eq_rename_frobenius g h0 j]
      by_cases hrange : e ∈ Set.range (Finsupp.mapDomain succEmb)
      · obtain ⟨e', rfl⟩ := hrange
        rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
        have hFg : ∀ k l, CartierModule.curve
            ((⇑(CartierModule.frobenius (p := p) (Φ := Φ)))^[k] (CartierModule.frobenius g)) l = 0 := by
          intro k l
          rw [← Function.iterate_succ_apply]
          exact hg (k + 1) l
        refine ih (CartierModule.frobenius g) hFg j e' ?_

        rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain] at hi
        obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
        exact ⟨i', hi', by simpa [succEmb] using hin⟩
      · exact coeff_rename_eq_zero _ _ hrange
  refine CartierModule.ext (funext fun j => ?_)
  ext e
  rw [CartierModule.toPowerSeries_zero]
  simp only [map_zero]
  by_cases he : e = 0
  · subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact f.constantCoeff_eq_zero j
  · obtain ⟨i, hi⟩ : e.support.Nonempty := Finsupp.support_nonempty_iff.mpr he
    exact main (i + 1) f h j e ⟨i, hi, Nat.lt_succ_self i⟩

end Expansion

section WittIdentity

def teichSum (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] (ρ : S) (k : ℕ) :
    WittVector p (Polynomial S) :=
  ∑ i ∈ Finset.range k, WittVector.teichmuller p (Polynomial.C (ρ ^ i) * Polynomial.X)

theorem teichSum_succ {S : Type*} [CommRing S] (ρ : S) (k : ℕ) :
    teichSum p ρ (k + 1) =
      teichSum p ρ k + WittVector.teichmuller p (Polynomial.C (ρ ^ k) * Polynomial.X) := by
  rw [teichSum, Finset.sum_range_succ]
  rfl

theorem teichSum_zero {S : Type*} [CommRing S] (ρ : S) : teichSum p ρ 0 = 0 := by
  rw [teichSum, Finset.sum_range_zero]

theorem map_teichSum {S T : Type*} [CommRing S] [CommRing T] (ψ : S →+* T) (ρ : S) (k : ℕ) :
    WittVector.map (Polynomial.mapRingHom ψ) (teichSum p ρ k) = teichSum p (ψ ρ) k := by
  rw [teichSum, teichSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WittVector.map_teichmuller, Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, map_pow]

theorem map_verschiebung_teichmuller_X_pow {S T : Type*} [CommRing S] [CommRing T] (ψ : S →+* T) :
    WittVector.map (Polynomial.mapRingHom ψ)
        (WittVector.verschiebung (WittVector.teichmuller p ((Polynomial.X : Polynomial S) ^ p))) =
      WittVector.verschiebung (WittVector.teichmuller p ((Polynomial.X : Polynomial T) ^ p)) := by
  rw [WittVector.map_verschiebung, WittVector.map_teichmuller, Polynomial.coe_mapRingHom,
    Polynomial.map_pow, Polynomial.map_X]

def zetaC (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem isPrimitiveRoot_zetaC : IsPrimitiveRoot (zetaC p) p :=
  Complex.isPrimitiveRoot_exp p hp.out.ne_zero

theorem teichSum_zetaC :
    teichSum p (zetaC p) p =
      WittVector.verschiebung (WittVector.teichmuller p ((Polynomial.X : Polynomial ℂ) ^ p)) := by
  have hζ := isPrimitiveRoot_zetaC (p := p)
  have hp' : ((p : ℕ) : Polynomial ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  letI : Invertible ((p : ℕ) : Polynomial ℂ) :=
    ⟨Polynomial.C ((p : ℂ)⁻¹), by
      rw [← map_natCast Polynomial.C, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
        map_one], by
      rw [← map_natCast Polynomial.C, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
        map_one]⟩
  apply (WittVector.ghostEquiv p (Polynomial ℂ)).injective
  funext n
  show WittVector.ghostMap (teichSum p (zetaC p) p) n = WittVector.ghostMap _ n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply, teichSum, map_sum]
  simp only [WittVector.ghostComponent_teichmuller]
  cases n with
  | zero =>
    rw [WittVector.ghostComponent_zero_verschiebung]
    simp only [pow_zero, pow_one]
    rw [← Finset.sum_mul, ← map_sum, hζ.geom_sum_eq_zero hp.out.one_lt, map_zero, zero_mul]
  | succ m =>
    rw [WittVector.ghostComponent_verschiebung, WittVector.ghostComponent_teichmuller, ← pow_mul,
      ← pow_succ']
    have hterm : ∀ i ∈ Finset.range p,
        (Polynomial.C (zetaC p ^ i) * (Polynomial.X : Polynomial ℂ)) ^ p ^ (m + 1) =
          Polynomial.X ^ p ^ (m + 1) := by
      intro i _
      rw [mul_pow, ← map_pow, ← pow_mul, pow_succ', ← mul_assoc, mul_comm i p, pow_mul, pow_mul,
        hζ.pow_eq_one, one_pow, one_pow, map_one, one_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

abbrev CycInt (p : ℕ) : Type := AdjoinRoot (Polynomial.cyclotomic p ℤ)

def cycIntToC : CycInt p →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (zetaC p) (by
    have h := (isPrimitiveRoot_zetaC (p := p)).isRoot_cyclotomic hp.out.pos
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← algebraMap_int_eq] at h
    exact h)

theorem cycIntToC_root : cycIntToC (AdjoinRoot.root (Polynomial.cyclotomic p ℤ)) = zetaC p :=
  AdjoinRoot.lift_root _

theorem cycIntToC_injective : Function.Injective (cycIntToC (p := p)) := by
  have hζ := isPrimitiveRoot_zetaC (p := p)
  intro a b hab
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    induction b using AdjoinRoot.induction_on with
    | ih h =>
      rw [cycIntToC, AdjoinRoot.lift_mk, AdjoinRoot.lift_mk] at hab
      apply AdjoinRoot.mk_eq_mk.mpr
      rw [Polynomial.cyclotomic_eq_minpoly hζ hp.out.pos]
      refine minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hp.out.pos) ?_
      rw [map_sub, Polynomial.aeval_def, Polynomial.aeval_def, hab, sub_self]

theorem teichSum_root :
    teichSum p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ)) p =
      WittVector.verschiebung
        (WittVector.teichmuller p ((Polynomial.X : Polynomial (CycInt p)) ^ p)) := by
  apply WittVector.map_injective (Polynomial.mapRingHom (cycIntToC (p := p)))
    (Polynomial.map_injective _ cycIntToC_injective)
  rw [map_teichSum, map_verschiebung_teichmuller_X_pow, cycIntToC_root]
  exact teichSum_zetaC

theorem teichSum_eq_verschiebung {S : Type*} [CommRing S] (ψ : CycInt p →+* S) :
    teichSum p (ψ (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))) p =
      WittVector.verschiebung (WittVector.teichmuller p ((Polynomial.X : Polynomial S) ^ p)) := by
  rw [← map_teichSum ψ, teichSum_root, map_verschiebung_teichmuller_X_pow]

end WittIdentity

section Iso

variable {S : Type v} [CommRing S] {d : ℕ} {Ψ : MvFormalGroup d S}

def IsIso (p : ℕ) [Fact p.Prime] (x : WittVector p (Polynomial S)) : Prop :=
  ∀ n, ∃ c : S, x.coeff n = Polynomial.C c * Polynomial.X ^ p ^ n

theorem isIso_zero : IsIso p (0 : WittVector p (Polynomial S)) :=
  fun n => ⟨0, by simp⟩

theorem isIso_teichmuller (a : S) :
    IsIso p (WittVector.teichmuller p (Polynomial.C a * Polynomial.X)) := by
  intro n
  cases n with
  | zero => exact ⟨a, by rw [WittVector.teichmuller_coeff_zero, pow_zero, pow_one]⟩
  | succ m => exact ⟨0, by rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos m), map_zero,
      zero_mul]⟩

theorem aeval_C_mul_X_pow_of_isWeightedHomogeneous {σ : Type*} (w : σ → ℕ) (φ : MvPolynomial σ ℤ)
    (m : ℕ) (hφ : MvPolynomial.IsWeightedHomogeneous w φ m) (c : σ → S) :
    MvPolynomial.aeval (fun v => Polynomial.C (c v) * Polynomial.X ^ w v) φ =
      Polynomial.C (MvPolynomial.aeval c φ) * Polynomial.X ^ m := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hw : Finsupp.weight w e = m := hφ (MvPolynomial.mem_support_iff.mp he)
  have hprod : ∏ i ∈ e.support, (Polynomial.C (c i) * Polynomial.X ^ w i) ^ e i =
      Polynomial.C (∏ i ∈ e.support, c i ^ e i) * Polynomial.X ^ m := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_prod, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_pow, ← map_pow, ← pow_mul, smul_eq_mul, mul_comm (e i) (w i)]
  rw [hprod, ← mul_assoc, Polynomial.algebraMap_apply, ← map_mul]

theorem isIso_add {x y : WittVector p (Polynomial S)} (hx : IsIso p x) (hy : IsIso p y) :
    IsIso p (x + y) := by
  choose cx hcx using hx
  choose cy hcy using hy
  intro n
  refine ⟨MvPolynomial.aeval (Function.uncurry ![cx, cy]) (WittVector.wittAdd p n), ?_⟩
  rw [WittVector.add_coeff]
  unfold WittVector.peval
  have hfam : (Function.uncurry ![x.coeff, y.coeff] : Fin 2 × ℕ → Polynomial S) =
      fun v => Polynomial.C (Function.uncurry ![cx, cy] v) *
        Polynomial.X ^ WittLaw.weight p (fun _ : Fin 2 => 1) v := by
    funext ⟨i, m⟩
    fin_cases i
    · show x.coeff m = Polynomial.C (cx m) * Polynomial.X ^ (1 * p ^ m)
      rw [one_mul, hcx]
    · show y.coeff m = Polynomial.C (cy m) * Polynomial.X ^ (1 * p ^ m)
      rw [one_mul, hcy]
  rw [hfam]
  exact aeval_C_mul_X_pow_of_isWeightedHomogeneous _ _ _ (WittLaw.isWeightedHomogeneous_wittAdd p n) _

theorem isIso_teichSum (ρ : S) (k : ℕ) : IsIso p (teichSum p ρ k) := by
  induction k with
  | zero => rw [teichSum_zero]; exact isIso_zero
  | succ k ih => rw [teichSum_succ]; exact isIso_add ih (isIso_teichmuller _)

def pt (x : WittVector p (Polynomial S)) : ℕ → PowerSeries S :=
  fun n => ((x.coeff n : Polynomial S) : PowerSeries S)

theorem coeff_pt_of_isIso {x : WittVector p (Polynomial S)} (hx : IsIso p x) (n : ℕ)
    (e : Unit →₀ ℕ) : ∃ c : S, MvPowerSeries.coeff e (pt x n) = if e () = p ^ n then c else 0 := by
  obtain ⟨c, hc⟩ := hx n
  refine ⟨c, ?_⟩
  rw [pt, coeff_coePoly, hc, Polynomial.coeff_C_mul_X_pow]

theorem constantCoeff_pt_of_isIso {x : WittVector p (Polynomial S)} (hx : IsIso p x) (n : ℕ) :
    MvPowerSeries.constantCoeff (pt x n) = 0 := by
  obtain ⟨c, hc⟩ := coeff_pt_of_isIso hx n 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc, if_neg]
  simp [(pow_pos hp.out.pos n).ne]

theorem hasSubst_pt_of_isIso {x : WittVector p (Polynomial S)} (hx : IsIso p x) :
    HasSubst (pt x) := by
  refine ⟨fun n => by rw [constantCoeff_pt_of_isIso hx]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (e () + 1)).subset fun n hn => ?_
  obtain ⟨c, hc⟩ := coeff_pt_of_isIso hx n e
  have hn' : MvPowerSeries.coeff e (pt x n) ≠ 0 := hn
  rw [hc] at hn'
  split_ifs at hn' with he
  · show n < e () + 1
    rw [he]
    exact Nat.lt_succ_of_lt (Nat.lt_pow_self hp.out.one_lt)
  · exact absurd rfl hn'

theorem subst_pairOf_pt_addFam {x y : WittVector p (Polynomial S)} (hx : IsIso p x)
    (hy : IsIso p y) (n : ℕ) :
    subst (pairOf (pt x) (pt y)) (WittLaw.addFam p S n) = pt (x + y) n := by
  have hR : pt (x + y) n = MvPolynomial.eval₂ (algebraMap ℤ (PowerSeries S))
      (fun v => ((Function.uncurry ![x.coeff, y.coeff] v : Polynomial S) : PowerSeries S))
      (WittVector.wittAdd p n) := by
    rw [pt, WittVector.add_coeff]
    unfold WittVector.peval
    rw [MvPolynomial.aeval_def]
    show (Polynomial.coeToPowerSeries.ringHom : Polynomial S →+* PowerSeries S)
        (MvPolynomial.eval₂ (algebraMap ℤ (Polynomial S)) (Function.uncurry ![x.coeff, y.coeff])
          (WittVector.wittAdd p n)) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [WittLaw.addFam, subst_coe, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap,
    MvPolynomial.aeval_def, hR]
  congr 1
  funext ⟨i, m⟩
  fin_cases i <;> rfl

variable [Ψ.IsComm]

theorem subst_pt_teichmuller_eq_zero (f' : CartierModule p Ψ) (h : ∀ l, CartierModule.curve f' l = 0)
    (a : S) (l : Fin d) :
    subst (pt (WittVector.teichmuller p (Polynomial.C a * Polynomial.X))) (f'.toPowerSeries l) = 0 := by
  set cst : Unit → PowerSeries S := fun _ => ((Polynomial.C a * Polynomial.X : Polynomial S) : PowerSeries S)
  have hcst : HasSubst cst := by
    refine hasSubst_of_constantCoeff_zero fun _ => ?_
    show MvPowerSeries.constantCoeff (((Polynomial.C a * Polynomial.X : Polynomial S)) : PowerSeries S) = 0
    rw [constantCoeff_coePoly, Polynomial.coeff_C_mul_X, if_neg (Nat.zero_ne_one)]
  have hfam : pt (WittVector.teichmuller p (Polynomial.C a * Polynomial.X)) =
      fun n => subst cst (CartierModule.curveFam S n) := by
    funext n
    cases n with
    | zero =>
      rw [pt, WittVector.teichmuller_coeff_zero]
      show cst () = subst cst (PowerSeries.X : PowerSeries S)
      rw [PowerSeries.X, subst_X hcst]
    | succ m =>
      rw [pt, WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos m), Polynomial.coe_zero]
      show (0 : PowerSeries S) = subst cst (0 : PowerSeries S)
      rw [← coe_substAlgHom hcst, map_zero]
  rw [hfam, ← subst_comp_subst_apply CartierModule.hasSubst_curveFam hcst, ← CartierModule.curve_apply,
    h l, ← coe_substAlgHom hcst, map_zero]

theorem subst_pt_teichSum_eq_zero (f' : CartierModule p Ψ) (h : ∀ l, CartierModule.curve f' l = 0)
    (ρ : S) (k : ℕ) (l : Fin d) :
    subst (pt (teichSum p ρ k)) (f'.toPowerSeries l) = 0 := by
  induction k generalizing l with
  | zero =>
    have h0 : pt (teichSum p ρ 0) = fun _ => (0 : PowerSeries S) := by
      funext n
      rw [teichSum_zero, pt, WittVector.zero_coeff, Polynomial.coe_zero]
    rw [h0]
    exact subst_zero_of_constantCoeff_eq_zero (f'.constantCoeff_eq_zero l)
  | succ k ih =>
    have hk : IsIso p (teichSum p ρ k) := isIso_teichSum ρ k
    have ht : IsIso p (WittVector.teichmuller p (Polynomial.C (ρ ^ k) * Polynomial.X)) :=
      isIso_teichmuller _
    rw [teichSum_succ]
    have hfam : pt (teichSum p ρ k + WittVector.teichmuller p (Polynomial.C (ρ ^ k) * Polynomial.X)) =
        fun n => subst (pairOf (pt (teichSum p ρ k))
          (pt (WittVector.teichmuller p (Polynomial.C (ρ ^ k) * Polynomial.X)))) (WittLaw.addFam p S n) :=
      funext fun n => (subst_pairOf_pt_addFam hk ht n).symm
    rw [hfam, subst_pair_addFam f' (hasSubst_pt_of_isIso hk) (hasSubst_pt_of_isIso ht) l]
    have h1 : (fun l' => subst (pt (teichSum p ρ k)) (f'.toPowerSeries l')) =
        fun _ => (0 : PowerSeries S) := funext ih
    have h2 : (fun l' => subst (pt (WittVector.teichmuller p (Polynomial.C (ρ ^ k) * Polynomial.X)))
        (f'.toPowerSeries l')) = fun _ => (0 : PowerSeries S) :=
      funext (subst_pt_teichmuller_eq_zero f' h (ρ ^ k))
    rw [h1, h2]
    exact subst_elim_zero_left Ψ (fun _ => map_zero _) l

def vcurveFam (S : Type v) [CommRing S] : ℕ → PowerSeries S
  | 0 => 0
  | m + 1 => CartierModule.curveFam S m

omit [Ψ.IsComm] in
theorem hasSubst_vcurveFam : HasSubst (vcurveFam S) := by
  refine ⟨fun n => ?_, fun e => ?_⟩
  · cases n with
    | zero => rw [vcurveFam, map_zero]; exact IsNilpotent.zero
    | succ m => rw [vcurveFam, CartierModule.constantCoeff_curveFam]; exact IsNilpotent.zero
  · refine (Set.finite_singleton 1).subset fun n hn => ?_
    match n, hn with
    | 0, hn => exact absurd (by simp [vcurveFam]) hn
    | 1, _ => rfl
    | m + 2, hn => exact absurd (by simp [vcurveFam, CartierModule.curveFam]) hn

theorem curve_frobenius_eq (f' : CartierModule p Ψ) (l : Fin d) :
    CartierModule.curve (CartierModule.frobenius f') l = subst (vcurveFam S) (f'.toPowerSeries l) := by
  rw [CartierModule.curve_apply, CartierModule.toPowerSeries_frobenius]
  show subst (CartierModule.curveFam S) (subst (WittLaw.verFam S) (f'.toPowerSeries l)) = _
  rw [subst_comp_subst_apply WittLaw.hasSubst_verFam CartierModule.hasSubst_curveFam]
  congr 1
  funext n
  cases n with
  | zero =>
    rw [WittLaw.verFam_zero, ← coe_substAlgHom CartierModule.hasSubst_curveFam, map_zero]
    rfl
  | succ m =>
    rw [WittLaw.verFam_succ, subst_X CartierModule.hasSubst_curveFam]
    rfl

theorem curve_frobenius_eq_zero_of_ringHom (ψ : CycInt p →+* S) (f' : CartierModule p Ψ)
    (h : ∀ l, CartierModule.curve f' l = 0) (l : Fin d) :
    CartierModule.curve (CartierModule.frobenius f') l = 0 := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set ρ : S := ψ (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))
  have hsum := subst_pt_teichSum_eq_zero f' h ρ p l
  rw [teichSum_eq_verschiebung ψ] at hsum

  set e : Unit → PowerSeries S := fun _ => (MvPowerSeries.X () : PowerSeries S) ^ p
  have he : HasSubst e := HasSubst.X_pow hp0
  have hfam : pt (WittVector.verschiebung (WittVector.teichmuller p ((Polynomial.X : Polynomial S) ^ p))) =
      fun n => subst e (vcurveFam S n) := by
    funext n
    match n with
    | 0 =>
      rw [pt, WittVector.verschiebung_coeff_zero, Polynomial.coe_zero, vcurveFam,
        ← coe_substAlgHom he, map_zero]
    | 1 =>
      rw [pt, WittVector.verschiebung_coeff_succ, WittVector.teichmuller_coeff_zero, Polynomial.coe_pow,
        Polynomial.coe_X, vcurveFam]
      show (PowerSeries.X : PowerSeries S) ^ p = subst e (PowerSeries.X : PowerSeries S)
      rw [PowerSeries.X, subst_X he]
    | m + 2 =>
      rw [pt, WittVector.verschiebung_coeff_succ,
        WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos m), Polynomial.coe_zero, vcurveFam]
      show (0 : PowerSeries S) = subst e (CartierModule.curveFam S (m + 1))
      rw [CartierModule.curveFam, ← coe_substAlgHom he, map_zero]
  rw [hfam, ← subst_comp_subst_apply hasSubst_vcurveFam he, ← curve_frobenius_eq] at hsum

  have hexp : MvPowerSeries.expand p hp0 (CartierModule.curve (CartierModule.frobenius f') l) = 0 := by
    rw [MvPowerSeries.expand, substAlgHom_apply]
    exact hsum
  refine MvPowerSeries.ext fun m => ?_
  have hm := congrArg (MvPowerSeries.coeff (p • m)) hexp
  rw [MvPowerSeries.coeff_expand_smul, map_zero] at hm
  rw [hm, map_zero]

end Iso

section Main

variable {R : Type u} [CommRing R] {d : ℕ}

abbrev CycExt (p : ℕ) (R : Type u) [CommRing R] : Type u := AdjoinRoot (Polynomial.cyclotomic p R)

theorem of_cyclotomic_injective :
    Function.Injective (AdjoinRoot.of (Polynomial.cyclotomic p R) : R → CycExt p R) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact fun a b _ => Subsingleton.elim a b
  intro a b hab
  have hmk : AdjoinRoot.mk (Polynomial.cyclotomic p R) (Polynomial.C a) =
      AdjoinRoot.mk (Polynomial.cyclotomic p R) (Polynomial.C b) := by
    rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C]
    exact hab
  rw [AdjoinRoot.mk_eq_mk, ← map_sub] at hmk
  by_contra hne
  have hne' : Polynomial.C (a - b) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero, sub_eq_zero]
    exact hne
  refine (Polynomial.cyclotomic.monic p R).not_dvd_of_natDegree_lt hne' ?_ hmk
  rw [Polynomial.natDegree_C, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]
  have := hp.out.two_le
  omega

def cycIntToCycExt : CycInt p →+* CycExt p R :=
  AdjoinRoot.lift (algebraMap ℤ (CycExt p R)) (AdjoinRoot.root (Polynomial.cyclotomic p R)) (by
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap R (AdjoinRoot.root (Polynomial.cyclotomic p R))
        (Polynomial.cyclotomic p ℤ),
      algebraMap_int_eq, Polynomial.map_cyclotomic_int, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

variable {Φ : MvFormalGroup d R} [Φ.IsComm]

theorem curve_frobenius_eq_zero (f : CartierModule p Φ) (h : ∀ l, CartierModule.curve f l = 0)
    (l : Fin d) : CartierModule.curve (CartierModule.frobenius f) l = 0 := by
  set i : R →+* CycExt p R := AdjoinRoot.of (Polynomial.cyclotomic p R)
  have hi : Function.Injective i := of_cyclotomic_injective
  set f' : CartierModule p (Φ.map i) := CartierModule.baseChange i f
  have h' : ∀ l, CartierModule.curve f' l = 0 := fun l => by
    show CartierModule.curve (CartierModule.baseChangeEq i rfl f) l = 0
    rw [CartierModule.curve_baseChangeEq, h l, map_zero]
  have key := curve_frobenius_eq_zero_of_ringHom (cycIntToCycExt (R := R)) f' h' l
  have hF : CartierModule.frobenius f' = CartierModule.baseChangeEq i rfl (CartierModule.frobenius f) :=
    (CartierModule.baseChangeEq_frobenius i rfl f).symm
  rw [hF, CartierModule.curve_baseChangeEq] at key
  ext n
  apply hi
  rw [← PowerSeries.coeff_map, key, map_zero, map_zero, map_zero]

theorem curve_frobenius_iterate_eq_zero (f : CartierModule p Φ) (h : ∀ l, CartierModule.curve f l = 0)
    (n : ℕ) (l : Fin d) :
    CartierModule.curve ((⇑(CartierModule.frobenius (p := p) (Φ := Φ)))^[n] f) l = 0 := by
  induction n generalizing l with
  | zero => exact h l
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact curve_frobenius_eq_zero _ ih l

theorem eq_zero_of_curve_eq_zero (f : CartierModule p Φ) (h : ∀ l, CartierModule.curve f l = 0) :
    f = 0 :=
  eq_zero_of_forall_curve_frobenius_iterate f (curve_frobenius_iterate_eq_zero f h)

theorem curve_sub (f g : CartierModule p Φ) (j : Fin d) :
    CartierModule.curve (f - g) j =
      subst (Sum.elim (CartierModule.curve f) (negSeries Φ (CartierModule.curve g)))
        (Φ.toPowerSeries j) := by
  have hg := g.constantCoeff_eq_zero
  have hneg : ∀ l, (negSeries Φ g.toPowerSeries l).constantCoeff = 0 := constantCoeff_negSeries Φ _
  have hC := CartierModule.hasSubst_curveFam (R := R)
  rw [CartierModule.curve_apply, CartierModule.toPowerSeries_sub]
  show subst (CartierModule.curveFam R)
      (subst (Sum.elim f.toPowerSeries (negSeries Φ g.toPowerSeries)) (Φ.toPowerSeries j)) = _
  rw [subst_subst_elim Φ f.constantCoeff_eq_zero hneg hC]

  have hnat : (fun l => subst (CartierModule.curveFam R) (negSeries Φ g.toPowerSeries l)) =
      negSeries Φ (CartierModule.curve g) := by
    refine negSeries_unique Φ (CartierModule.constantCoeff_curve g)
      (fun l => constantCoeff_subst_eq_zero hC CartierModule.constantCoeff_curveFam (hneg l))
      fun i => ?_
    have h1 := subst_subst_elim Φ hg hneg hC i
    have h2 : subst (Sum.elim g.toPowerSeries (negSeries Φ g.toPowerSeries)) (Φ.toPowerSeries i) = 0 :=
      subst_elim_negSeries Φ hg i
    have hz : subst (CartierModule.curveFam R) (0 : MvPowerSeries ℕ R) = 0 := by
      rw [← coe_substAlgHom hC, map_zero]
    rw [h2, hz] at h1
    exact h1.symm
  rw [hnat]
  rfl

theorem curve_injective :
    Function.Injective (CartierModule.curve : CartierModule p Φ → Fin d → PowerSeries R) := by
  intro f g hfg
  have hzero : ∀ j, CartierModule.curve (f - g) j = 0 := by
    intro j
    rw [curve_sub, hfg]
    exact subst_elim_negSeries Φ (CartierModule.constantCoeff_curve g) j
  exact sub_eq_zero.mp (eq_zero_of_curve_eq_zero (f - g) hzero)

end Main

end CurveInjSol
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt.CurveInjSol"

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective
      (MvFormalGroup.CartierModule.curve : MvFormalGroup.CartierModule p Φ → Fin d → PowerSeries R) :=
  CurveInjSol.curve_injective

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt.CurveInjSol"

end S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt (solution)
