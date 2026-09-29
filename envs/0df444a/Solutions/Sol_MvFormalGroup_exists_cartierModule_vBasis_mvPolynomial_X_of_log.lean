-- Prove2me | solution 1 for MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d8e42b36-d527-52a5-bb82-30c69a31c74c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvFormalGroup_WittLaw_coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost
import Theorems.Thm_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
import Theorems.Thm_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
import Theorems.Thm_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open MvPowerSeries

noncomputable section

namespace U4Asm

section LogReadout

variable {p : ℕ} [hp : Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
  {Φ : MvFormalGroup d 𝓞} [Φ.IsComm]
  (f : Fin d → MvPowerSeries (Fin d) 𝓞)

def L (m : MvFormalGroup.CartierModule p Φ) : Fin d → MvPowerSeries ℕ 𝓞 :=
  fun j => subst m.toPowerSeries (f j)

theorem L_apply (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f m j = subst m.toPowerSeries (f j) := rfl

variable (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))

include hlog in
theorem L_add (m m' : MvFormalGroup.CartierModule p Φ) : L f (m + m') = L f m + L f m' := by
  funext j
  have hm := m.constantCoeff_eq_zero
  have hm' := m'.constantCoeff_eq_zero
  have hE : HasSubst (Sum.elim m.toPowerSeries m'.toPowerSeries) :=
    MvFormalGroup.hasSubst_elim hm hm'
  have hinl : HasSubst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hinr : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  show subst (m + m').toPowerSeries (f j) = subst m.toPowerSeries (f j) + subst m'.toPowerSeries (f j)
  rw [MvFormalGroup.CartierModule.toPowerSeries_add,
    ← subst_comp_subst_apply Φ.hasSubst_toPowerSeries hE, hlog j, subst_add hE,
    subst_comp_subst_apply hinl hE, subst_comp_subst_apply hinr hE]
  simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]

include hlog in
theorem L_zero : L f (0 : MvFormalGroup.CartierModule p Φ) = 0 := by
  have h := L_add f hlog (0 : MvFormalGroup.CartierModule p Φ) 0
  rw [add_zero] at h
  exact left_eq_add.mp h |>.symm ▸ rfl

def Lhom : MvFormalGroup.CartierModule p Φ →+ (Fin d → MvPowerSeries ℕ 𝓞) where
  toFun := L f
  map_zero' := L_zero f hlog
  map_add' := L_add f hlog

@[scoped simp] theorem Lhom_apply (m : MvFormalGroup.CartierModule p Φ) : Lhom f hlog m = L f m := rfl

omit hlog in
theorem L_precomp {v : ℕ → MvPowerSeries ℕ 𝓞} (hv : MvFormalGroup.WittLaw.IsEndo p v)
    (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (MvFormalGroup.CartierModule.precomp hv m) j = subst v (L f m j) := by
  show subst (fun i => subst v (m.toPowerSeries i)) (f j) = subst v (subst m.toPowerSeries (f j))
  rw [subst_comp_subst_apply m.hasSubst_toPowerSeries hv.hasSubst]

omit hlog in
theorem L_frobenius (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (MvFormalGroup.CartierModule.frobenius m) j =
      subst (MvFormalGroup.WittLaw.verFam 𝓞) (L f m j) :=
  L_precomp f MvFormalGroup.WittLaw.isEndo_verFam m j

omit hlog in
theorem L_verschiebungInt (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (MvFormalGroup.CartierModule.verschiebungInt m) j =
      subst (MvFormalGroup.WittLaw.frobPolyFam p 𝓞) (L f m j) :=
  L_precomp f MvFormalGroup.WittLaw.isEndo_frobPolyFam m j

omit hlog in
theorem L_homothety (a : 𝓞) (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (MvFormalGroup.CartierModule.homothety a m) j =
      subst (MvFormalGroup.WittLaw.teichFam p a) (L f m j) :=
  L_precomp f (MvFormalGroup.WittLaw.isEndo_teichFam a) m j

variable (ψ : Fin d → MvPowerSeries (Fin d) 𝓞) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
  (hψf : ∀ i, subst f (ψ i) = X i)

include hψf in
omit hlog in
theorem L_injective (hf0 : ∀ i, (f i).constantCoeff = 0) :
    Function.Injective (L (p := p) (Φ := Φ) f) := by
  intro m m' h
  apply MvFormalGroup.CartierModule.ext
  funext j
  have hf : HasSubst f := hasSubst_of_constantCoeff_zero hf0
  have key : ∀ n : MvFormalGroup.CartierModule p Φ,
      n.toPowerSeries j = subst (L f n) (ψ j) := by
    intro n
    have := congrArg (subst n.toPowerSeries) (hψf j)
    rw [subst_X n.hasSubst_toPowerSeries, subst_comp_subst_apply hf n.hasSubst_toPowerSeries] at this
    exact this.symm
  rw [key m, key m', h]

end LogReadout

section Ghost

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def IsGh (c : ℕ → R) (G : MvPowerSeries ℕ R) : Prop :=
  (∀ k n : ℕ, (coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n)) ∧
  (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (coeff e G : R) = 0)

variable {p}

theorem IsGh.ext {c : ℕ → R} {G G' : MvPowerSeries ℕ R} (h : IsGh p c G) (h' : IsGh p c G') :
    G = G' := by
  ext e
  by_cases he : ∃ k n : ℕ, e = Finsupp.single k (p ^ n)
  · obtain ⟨k, n, rfl⟩ := he
    rw [h.1, h'.1]
  · push Not at he
    rw [h.2 e he, h'.2 e he]

theorem IsGh.congr {c c' : ℕ → R} {G : MvPowerSeries ℕ R} (h : IsGh p c G)
    (hcc : ∀ N, c N = c' N) : IsGh p c' G :=
  ⟨fun k n => by rw [h.1, hcc], h.2⟩

theorem IsGh.add {c c' : ℕ → R} {G G' : MvPowerSeries ℕ R} (h : IsGh p c G)
    (h' : IsGh p c' G') : IsGh p (fun N => c N + c' N) (G + G') :=
  ⟨fun k n => by rw [map_add, h.1, h'.1, mul_add],
    fun e he => by rw [map_add, h.2 e he, h'.2 e he, add_zero]⟩

theorem IsGh.zero : IsGh p (fun _ => (0 : R)) (0 : MvPowerSeries ℕ R) :=
  ⟨fun k n => by simp, fun e _ => by simp⟩

theorem IsGh.sum {ι : Type*} (s : Finset ι) (c : ι → ℕ → R) (G : ι → MvPowerSeries ℕ R)
    (h : ∀ i ∈ s, IsGh p (c i) (G i)) :
    IsGh p (fun N => ∑ i ∈ s, c i N) (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsGh.zero (p := p) (R := R))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have := (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine this.congr fun N => ?_
    rw [Finset.sum_insert ha]

theorem IsGh.verFam {c : ℕ → R} {G : MvPowerSeries ℕ R} (h : IsGh p c G) :
    IsGh p (fun N => (p : R) * c (N + 1)) (subst (MvFormalGroup.WittLaw.verFam R) G) :=
  (MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost p c G h.1 h.2).1

theorem IsGh.frobPolyFam {c : ℕ → R} {G : MvPowerSeries ℕ R} (h : IsGh p c G) :
    IsGh p (fun N => if N = 0 then 0 else c (N - 1))
      (subst (MvFormalGroup.WittLaw.frobPolyFam p R) G) :=
  (MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost p c G h.1 h.2).2.1

theorem IsGh.teichFam {c : ℕ → R} {G : MvPowerSeries ℕ R} (h : IsGh p c G) (a : R) :
    IsGh p (fun N => a ^ p ^ N * c N) (subst (MvFormalGroup.WittLaw.teichFam p a) G) :=
  (MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost p c G h.1 h.2).2.2 a

theorem IsGh.frobPolyFam_iterate {c : ℕ → R} {G : MvPowerSeries ℕ R} (h : IsGh p c G) (m : ℕ) :
    IsGh p (fun N => if N < m then 0 else c (N - m))
      ((subst (MvFormalGroup.WittLaw.frobPolyFam p R))^[m] G) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ih.frobPolyFam.congr fun N => ?_
    by_cases hN : N = 0
    · subst hN; simp
    · rw [if_neg hN]
      by_cases hNm : N - 1 < m
      · rw [if_pos hNm, if_pos (by omega)]
      · rw [if_neg hNm, if_neg (by omega)]
        congr 1
        omega

end Ghost

section Concrete

variable (p : ℕ) [hp : Fact p.Prime] (d : ℕ)

local notation "𝕂" => MvPolynomial (ℕ × Fin d × Fin d) (Padic p)
local notation "𝔸" => MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)

abbrev iota : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) →+* MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
  MvPolynomial.map (PadicInt.Coe.ringHom (p := p))

theorem iota_injective : Function.Injective (iota p d) :=
  MvPolynomial.map_injective _ Subtype.coe_injective

def Aint : Subring (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) := (iota p d).range

def sigK : MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →+* MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
  (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom

def sig0 : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) →+* MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) :=
  (MvPolynomial.aeval fun v => MvPolynomial.X v ^ p).toRingHom

theorem coe_sigK : (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
    MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
      = ⇑(sigK p d) := rfl

theorem sigK_comp_iota : (sigK p d).comp (iota p d) = (iota p d).comp (sig0 p d) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [sigK, sig0, iota]
  · intro v; simp [sigK, sig0, iota]

theorem sigK_mem_A {x : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)} (hx : x ∈ Aint p d) :
    sigK p d x ∈ Aint p d := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨sig0 p d q, (congrArg (fun φ => φ q) (sigK_comp_iota p d)).symm⟩

theorem X_mem_A (v : ℕ × Fin d × Fin d) :
    (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ∈ Aint p d :=
  ⟨MvPolynomial.X v, by simp [iota]⟩

theorem natCast_mem_A (n : ℕ) :
    ((n : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))) ∈ Aint p d := natCast_mem (Aint p d) n

theorem sigK_iterate_mem_A {x : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)}
    (hx : x ∈ Aint p d) (m : ℕ) : (⇑(sigK p d))^[m] x ∈ Aint p d := by
  induction m with
  | zero => exact hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact sigK_mem_A p d ih

theorem sigK_natCast (n : ℕ) : sigK p d n = n := map_natCast _ n

theorem sigK_iterate_natCast (m n : ℕ) : (⇑(sigK p d))^[m] (n : 𝕂) = n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, sigK_natCast]

theorem sigK_X (v : ℕ × Fin d × Fin d) : sigK p d (MvPolynomial.X v) = MvPolynomial.X v ^ p := by
  simp [sigK]

theorem sigK_iterate_X (m : ℕ) (v : ℕ × Fin d × Fin d) :
    (⇑(sigK p d))^[m] (MvPolynomial.X v) = MvPolynomial.X v ^ p ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_pow, sigK_X, ← pow_mul, ← pow_succ']

theorem sigK_iterate_mul (m : ℕ) (x y : 𝕂) :
    (⇑(sigK p d))^[m] (x * y) = (⇑(sigK p d))^[m] x * (⇑(sigK p d))^[m] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem sigK_iterate_add (m n : ℕ) (x : 𝕂) :
    (⇑(sigK p d))^[m] ((⇑(sigK p d))^[n] x) = (⇑(sigK p d))^[m + n] x :=
  (Function.iterate_add_apply _ m n x).symm

section LogCoeff

variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
variable (h1 : a 0 = 1)
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])

include h2 in

theorem h2_entry (k : ℕ) (i j : Fin d) :
    (p : 𝕂) * a (k + 1) i j
      = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
          MvPolynomial.X (m, i, l) * (⇑(sigK p d))^[m + 1] (a (k - m) l j) := by
  have h := congrArg (fun M => M i j) (h2 k)
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, coe_sigK] at h
  exact h

include h1 h2 in

theorem pow_mul_logCoeff_mem (k : ℕ) (i j : Fin d) :
    (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * a k i j ∈ Aint p d := by
  induction k using Nat.strong_induction_on generalizing i j with
  | _ k ih =>
    match k with
    | 0 =>
        rw [pow_zero, one_mul, h1]
        by_cases hij : i = j
        · subst hij; rw [Matrix.one_apply_eq]; exact (Aint p d).one_mem
        · rw [Matrix.one_apply_ne hij]; exact (Aint p d).zero_mem
    | (k + 1) =>
        have hentry := h2_entry p d a h2 k i j
        have hpush : ∀ (n : ℕ) (y : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)),
            (p : 𝕂) ^ k * (⇑(sigK p d))^[n] y = (⇑(sigK p d))^[n] ((p : 𝕂) ^ k * y) := by
          intro n y
          rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
        have hmain : (p : 𝕂) ^ (k + 1) * a (k + 1) i j
            = ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
                MvPolynomial.X (m, i, l) * (⇑(sigK p d))^[m + 1] ((p : 𝕂) ^ k * a (k - m) l j) := by
          have hstep : (p : 𝕂) ^ (k + 1) * a (k + 1) i j = (p : 𝕂) ^ k * ((p : 𝕂) * a (k + 1) i j) := by
            ring
          rw [hstep, hentry, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [mul_left_comm, hpush]
        rw [hmain]
        refine Subring.sum_mem _ fun m hm => Subring.sum_mem _ fun l _ => ?_
        refine (Aint p d).mul_mem (X_mem_A p d _) ?_
        have hk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hsplit : (p : 𝕂) ^ k * a (k - m) l j = (p : 𝕂) ^ m * ((p : 𝕂) ^ (k - m) * a (k - m) l j) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega
        rw [hsplit]
        exact sigK_iterate_mem_A p d
          ((Aint p d).mul_mem ((Aint p d).pow_mem (natCast_mem_A p d p) m)
            (ih (k - m) (by omega) l j)) (m + 1)

include h1 h2 in
theorem pow_mul_logCoeff_mem_of_le {k s : ℕ} (hs : s ≤ k) (i j : Fin d) :
    (p : 𝕂) ^ k * a s i j ∈ Aint p d := by
  have : (p : 𝕂) ^ k * a s i j = (p : 𝕂) ^ (k - s) * ((p : 𝕂) ^ s * a s i j) := by
    rw [← mul_assoc, ← pow_add]; congr 2; omega
  rw [this]
  exact (Aint p d).mul_mem ((Aint p d).pow_mem (natCast_mem_A p d p) _)
    (pow_mul_logCoeff_mem p d a h1 h2 s i j)

end LogCoeff

end Concrete

section Helpers

variable {p : ℕ} [hp : Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S]

theorem map_frobPolyFam (g : R →+* S) (n : ℕ) :
    MvPowerSeries.map g (MvFormalGroup.WittLaw.frobPolyFam p R n) =
      MvFormalGroup.WittLaw.frobPolyFam p S n := by
  have hc : g.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  rw [MvFormalGroup.WittLaw.frobPolyFam_apply, MvFormalGroup.WittLaw.frobPolyFam_apply,
    MvFormalGroup.WittLaw.frobPoly_eq_map, MvFormalGroup.WittLaw.frobPoly_eq_map,
    ← MvFormalGroup.WittLaw.coe_mvPolynomial_map, MvPolynomial.map_map, hc]

variable {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm] {Ψ : MvFormalGroup d S} [Ψ.IsComm]

theorem baseChangeEq_verschiebungInt_iterate (g : R →+* S) (h : Φ.map g = Ψ) (n : ℕ)
    (m : MvFormalGroup.CartierModule p Φ) :
    MvFormalGroup.CartierModule.baseChangeEq g h
        ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] m) =
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[n]
        (MvFormalGroup.CartierModule.baseChangeEq g h m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    exact MvFormalGroup.CartierModule.baseChangeEq_precomp g h
      MvFormalGroup.WittLaw.isEndo_frobPolyFam MvFormalGroup.WittLaw.isEndo_frobPolyFam
      (map_frobPolyFam g) m

end Helpers

section LMore

variable {p : ℕ} [hp : Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
  {Φ : MvFormalGroup d 𝓞} [Φ.IsComm]
  (f : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))

include hlog in
theorem L_sum {ι : Type*} (s : Finset ι) (g : ι → MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (∑ x ∈ s, g x) j = ∑ x ∈ s, L f (g x) j := by
  have := map_sum (Lhom f hlog) g s
  rw [Lhom_apply] at this
  rw [this, Finset.sum_apply]
  rfl

include hlog in
theorem L_add_apply (m m' : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f (m + m') j = L f m j + L f m' j := by
  rw [L_add f hlog]; rfl

omit hlog in
theorem L_verschiebungInt_iterate (n : ℕ) (m : MvFormalGroup.CartierModule p Φ) (j : Fin d) :
    L f ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] m) j =
      (subst (MvFormalGroup.WittLaw.frobPolyFam p 𝓞))^[n] (L f m j) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, L_verschiebungInt]

end LMore

section Tail

variable (p : ℕ) [hp : Fact p.Prime] (d : ℕ)

local notation "𝕂" => MvPolynomial (ℕ × Fin d × Fin d) (Padic p)

variable (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))

def bb (i : Fin d) (N : ℕ) : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
  fun M j' => ∑ m ∈ Finset.Ico N (M + N + 1), ∑ j : Fin d,
    MvPolynomial.X (m, j, i) ^ p ^ (M + N - m) * a (M + N - m) j' j

variable (h1 : a 0 = 1)
variable (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])

include h1 h2 in
theorem pow_mul_bb_mem (i : Fin d) (N M : ℕ) (j' : Fin d) :
    (p : 𝕂) ^ M * bb p d a i N M j' ∈ Aint p d := by
  unfold bb
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun m hm => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [mul_left_comm]
  refine (Aint p d).mul_mem ((Aint p d).pow_mem (X_mem_A p d _) _) ?_
  have hmN : N ≤ m := (Finset.mem_Ico.mp hm).1
  exact pow_mul_logCoeff_mem_of_le p d a h1 h2 (by omega) j' j

theorem sigK_pow_X_pow (n e : ℕ) (v : ℕ × Fin d × Fin d) :
    ((sigK p d) ^ n) (MvPolynomial.X v ^ e) = MvPolynomial.X v ^ (e * p ^ n) := by
  rw [map_pow, RingHom.coe_pow, sigK_iterate_X, ← pow_mul, mul_comm]

include h1 h2 in

theorem tail_FE (i : Fin d) (N k : ℕ) (j' : Fin d) :
    (p : 𝕂) * bb p d a i N (k + 1) j'
      - ∑ m' ∈ Finset.range (k + 1), ∑ l : Fin d,
          MvPolynomial.X (m', j', l) * (⇑(sigK p d))^[m' + 1] (bb p d a i N (k - m') l)
      = (p : 𝕂) * MvPolynomial.X (k + N + 1, j', i) := by

  have hsplit : (p : 𝕂) * bb p d a i N (k + 1) j'
      = (p : 𝕂) * MvPolynomial.X (k + N + 1, j', i)
        + ∑ m ∈ Finset.Ico N (k + N + 1), ∑ j : Fin d,
            MvPolynomial.X (m, j, i) ^ p ^ (k + N - m + 1) * ((p : 𝕂) * a (k + N - m + 1) j' j) := by
    unfold bb
    rw [show k + 1 + N + 1 = (k + N + 1) + 1 by ring,
      Finset.sum_Ico_succ_top (by omega : N ≤ k + N + 1), mul_add, add_comm]
    congr 1
    · rw [show k + 1 + N - (k + N + 1) = 0 by omega, h1, pow_zero, Finset.mul_sum]
      simp only [pow_one, Matrix.one_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hmk : m ≤ k + N := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hm).2
      rw [show k + 1 + N - m = k + N - m + 1 by omega, mul_left_comm]
  rw [hsplit, add_sub_assoc, add_eq_left, sub_eq_zero]

  simp_rw [h2_entry p d a h2]

  conv_rhs =>
    arg 2; ext m'; arg 2; ext l
    rw [bb, ← RingHom.coe_pow, map_sum]
  simp_rw [map_sum, map_mul, sigK_pow_X_pow, RingHom.coe_pow]

  simp_rw [Finset.mul_sum]

  rw [Finset.sum_congr rfl fun m _ => Finset.sum_comm]
  rw [Finset.sum_comm' (s' := fun m' => Finset.Ico N (k - m' + N + 1)) (t' := Finset.range (k + 1))
    (h := fun m m' => by
      simp only [Finset.mem_Ico, Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hm'k : m' ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')
  have hmN : N ≤ m ∧ m ≤ k - m' + N := by
    have := Finset.mem_Ico.mp hm; omega
  rw [show k - m' + N - m = k + N - m - m' by omega, ← pow_add,
    show k + N - m - m' + (m' + 1) = k + N - m + 1 by omega]
  ring

include h1 h2 in

theorem key_seq (i j' : Fin d) (N M : ℕ) :
    (∑ m : Fin N, if M < (m : ℕ) then 0 else
        ∑ j : Fin d, (iota p d (MvPolynomial.X ((m : ℕ), j, i))) ^ p ^ (M - m) * a (M - m) j' j)
      + (if M < N then 0 else bb p d a i N (M - N) j')
      = (p : 𝕂) * a (M + 1) j' i := by
  have hRR :=
    MvFormalGroup.smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
      p d a h1 h2 M
  have hentry := congrArg (fun A => A j' i) hRR
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply, Matrix.map_apply,
    Matrix.of_apply, coe_sigK, sigK_iterate_X] at hentry
  rw [hentry]
  simp only [MvPolynomial.map_X]

  set F : ℕ → 𝕂 := fun m => ∑ j : Fin d, MvPolynomial.X (m, j, i) ^ p ^ (M - m) * a (M - m) j' j with hF
  have hrhs : ∑ m ∈ Finset.range (M + 1), ∑ j : Fin d, a (M - m) j' j * MvPolynomial.X (m, j, i) ^ p ^ (M - m)
      = ∑ m ∈ Finset.range (M + 1), F m := by
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hrhs]
  have hlhs1 : (∑ m : Fin N, if M < (m : ℕ) then 0 else
        ∑ j : Fin d, MvPolynomial.X ((m : ℕ), j, i) ^ p ^ (M - m) * a (M - m) j' j)
      = ∑ m ∈ Finset.range N, if m ≤ M then F m else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : M < (m : ℕ)
    · rw [if_pos h, if_neg (show ¬ ((m : ℕ) ≤ M) by omega)]
    · rw [if_neg h, if_pos (show (m : ℕ) ≤ M by omega)]
  rw [hlhs1, ← Finset.sum_filter]
  by_cases hMN : M < N
  · rw [if_pos hMN, add_zero]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [if_neg hMN]
    have hfilt : (Finset.range N).filter (fun m => m ≤ M) = Finset.range N := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt]
    have hb : bb p d a i N (M - N) j' = ∑ m ∈ Finset.Ico N (M + 1), F m := by
      unfold bb
      rw [show M - N + N = M by omega]
    rw [hb, Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive F (Nat.zero_le N) (by omega : N ≤ M + 1)

end Tail

section Main

variable (p : ℕ) [hp : Fact p.Prime] (d : ℕ)

local notation "𝕂" => MvPolynomial (ℕ × Fin d × Fin d) (Padic p)
local notation "𝔸" => MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)

set_option maxHeartbeats 1600000 in

theorem main
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀).toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ (γ : Fin d → MvFormalGroup.CartierModule p Φ₀),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ₀,
        MvFormalGroup.CartierModule.frobenius (γ i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), j, i) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (γ j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[N] h := by
  classical

  have hf0 : ∀ i, (f i).constantCoeff = 0 := by
    intro i
    have h := h4 i 0 (fun j k hjk => by
      have := congrArg (fun e : Fin d →₀ ℕ => e j) hjk
      simp at this
      exact absurd this (pow_pos hp.out.pos k).ne)
    simpa using h
  have hlin : MvFormalGroup.linearPart f = 1 := by
    ext i j
    simp only [MvFormalGroup.linearPart, Matrix.of_apply]
    have := h3 i j 0
    rw [pow_zero] at this
    rw [this, h1]
  have hf1 : ∀ i j : Fin d, (coeff (Finsupp.single j 1) (f i) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
      = if i = j then 1 else 0 := by
    intro i j
    have := h3 i j 0
    rw [pow_zero] at this
    rw [this, h1, Matrix.one_apply]
  obtain ⟨ψ, hψ0, hψf, hfψ⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one f hf0 hlin
  have hι : Function.Injective (iota p d) := iota_injective p d

  have hK : ∀ i : Fin d, ∃ m : MvFormalGroup.CartierModule p (MvFormalGroup.map (iota p d) Φ₀),
      (∀ j, MvFormalGroup.CartierModule.tangent m j = a 0 j i) ∧
      (∀ j, IsGh p (fun N => a N j i) (L f m j)) := by
    intro i
    obtain ⟨m, ht, hg1, hg2⟩ :=
      MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
        p (MvFormalGroup.map (iota p d) Φ₀) f ψ hf0 hf1 hψ0 hfψ hψf h5 (fun N j => a N j i)
    exact ⟨m, ht, fun j => ⟨fun k n => hg1 j k n, fun e he => hg2 j e he⟩⟩
  choose mK hmK_tan hmK_gh using hK

  have hA : ∀ i : Fin d, ∃ γ : MvFormalGroup.CartierModule p Φ₀,
      MvFormalGroup.CartierModule.baseChangeEq (iota p d) rfl γ = mK i := by
    intro i
    refine MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
      p d Φ₀ a f h1 h2 h3 h4 (fun N j => a N j i) ?_ ?_ (mK i)
      (fun j k n => (hmK_gh i j).1 k n) (fun j e he => (hmK_gh i j).2 e he)
    · intro N j
      obtain ⟨r, hr⟩ := pow_mul_logCoeff_mem p d a h1 h2 N j i
      exact ⟨r, hr.symm⟩
    · intro k j
      refine ⟨0, ?_⟩
      rw [map_zero, mul_zero, sub_eq_zero, h2_entry p d a h2 k j i]
      rfl
  choose γ hγ using hA
  refine ⟨γ, ?_, ?_⟩
  ·
    have hmat : (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k) = 1 := by
      refine Matrix.ext fun i k => ?_
      rw [Matrix.of_apply]
      apply hι
      have := congrArg (fun v => v k)
        (MvFormalGroup.CartierModule.tangent_baseChangeEq (p := p) (iota p d) rfl (γ i))
      simp only at this
      rw [hγ i, hmK_tan] at this
      rw [← this, h1]
      by_cases hik : i = k
      · subst hik; simp
      · rw [Matrix.one_apply_ne hik, Matrix.one_apply_ne (Ne.symm hik), map_zero]
    rw [hmat, Matrix.det_one]
    exact isUnit_one
  ·
    intro i N

    obtain ⟨mh, -, hmh1, hmh2⟩ :=
      MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
        p (MvFormalGroup.map (iota p d) Φ₀) f ψ hf0 hf1 hψ0 hfψ hψf h5 (bb p d a i N)
    have hb_gh : ∀ j, IsGh p (fun M => bb p d a i N M j) (L f mh j) := fun j => ⟨hmh1 j, hmh2 j⟩
    have hbA : ∀ (M : ℕ) (j' : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
        (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ M * bb p d a i N M j' = iota p d r := by
      intro M j'
      obtain ⟨r, hr⟩ := pow_mul_bb_mem p d a h1 h2 i N M j'
      exact ⟨r, hr.symm⟩
    have hbFE : ∀ (k : ℕ) (j' : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
        (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * bb p d a i N (k + 1) j'
          - ∑ m' ∈ Finset.range (k + 1), ∑ l : Fin d,
              MvPolynomial.X (m', j', l) *
                ((⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                    MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p]
                      MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))^[m' + 1]) (bb p d a i N (k - m') l)
          = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * iota p d r := by
      intro k j'
      refine ⟨MvPolynomial.X (k + N + 1, j', i), ?_⟩
      rw [coe_sigK, tail_FE p d a h1 h2 i N k j', MvPolynomial.map_X]
    obtain ⟨h, hh⟩ :=
      MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
        p d Φ₀ a f h1 h2 h3 h4 (bb p d a i N) hbA hbFE mh hmh1 hmh2
    refine ⟨h, ?_⟩
    have hh' : MvFormalGroup.CartierModule.baseChangeEq (iota p d) rfl h = mh := hh

    apply MvFormalGroup.CartierModule.baseChangeEq_injective (p := p) (iota p d) rfl hι
    rw [map_add, map_sum, MvFormalGroup.CartierModule.baseChangeEq_frobenius,
      baseChangeEq_verschiebungInt_iterate, hγ i, hh']
    simp_rw [baseChangeEq_verschiebungInt_iterate, map_sum,
      MvFormalGroup.CartierModule.baseChangeEq_homothety, hγ]

    apply L_injective f ψ hψf hf0
    funext j'
    refine IsGh.ext (p := p) (c := fun M => (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * a (M + 1) j' i) ?_ ?_
    · rw [L_frobenius]
      exact (hmK_gh i j').verFam
    · rw [L_add_apply f h5, L_sum f h5, L_verschiebungInt_iterate]
      simp_rw [L_verschiebungInt_iterate, L_sum f h5, L_homothety]
      have hR := IsGh.add
        (IsGh.sum (p := p) (Finset.univ : Finset (Fin N)) _ _ fun m _ =>
          (IsGh.sum (p := p) (Finset.univ : Finset (Fin d)) _ _ fun j _ =>
            (hmK_gh j j').teichFam (iota p d (MvPolynomial.X ((m : ℕ), j, i)))).frobPolyFam_iterate m)
        ((hb_gh j').frobPolyFam_iterate N)
      refine hR.congr fun M => ?_
      rw [← key_seq p d a h1 h2 i j' N M]

end Main

end U4Asm
p2m_reactivate "P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log.U4Asm"

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log.U4Asm"

theorem solution
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀).toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ (γ : Fin d → MvFormalGroup.CartierModule p Φ₀),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ₀,
        MvFormalGroup.CartierModule.frobenius (γ i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), j, i) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (γ j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[N] h :=
  U4Asm.main p d Φ₀ a f h1 h2 h3 h4 h5

end S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log
end P2MW
export P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log (solution)
