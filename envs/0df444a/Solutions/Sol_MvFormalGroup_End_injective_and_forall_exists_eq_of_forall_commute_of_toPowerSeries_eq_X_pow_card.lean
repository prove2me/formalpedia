-- Prove2me | solution 1 for MvFormalGroup.End.injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c807b9c4-83ae-5666-bf55-ba2ba2e9c435

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v

noncomputable section

open MvPowerSeries

namespace P2mKcCommutantLT

variable {p : ℕ} [Fact p.Prime]

theorem hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero

theorem hpn0 (n : ℕ) : p ^ n ≠ 0 := pow_ne_zero n hp0

section Series

variable {k : Type v} [Field k] [CharP k p] {σ : Type*}

theorem pow_p_eq_expand_map (f : MvPowerSeries σ k) :
    f ^ p = expand p hp0 (map (frobenius k p) f) := by
  rw [← map_frobenius_expand p hp0, map_expand]

theorem pow_pow_eq_expand_map (f : MvPowerSeries σ k) (n : ℕ) :
    f ^ p ^ n = expand (p ^ n) (hpn0 n) (map (iterateFrobenius k p n) f) := by
  rw [← map_iterateFrobenius_expand p hp0 f n, map_expand]

theorem expand_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (expand n hn : MvPowerSeries σ k → MvPowerSeries σ k) := by
  intro f g hfg
  ext m
  have := congrArg (coeff (n • m)) hfg
  rwa [coeff_expand_smul, coeff_expand_smul] at this

theorem map_map_apply {S T : Type*} [CommRing S] [CommRing T] (f : k →+* S) (g : S →+* T)
    (x : MvPowerSeries σ k) : map g (map f x) = map (g.comp f) x := by
  ext m; simp only [coeff_map, RingHom.comp_apply]

theorem map_frobenius_map_iterateFrobenius (x : MvPowerSeries σ k) (n : ℕ) :
    map (frobenius k p) (map (iterateFrobenius k p n) x) = map (iterateFrobenius k p (n + 1)) x := by
  ext m
  simp only [coeff_map, frobenius_def, iterateFrobenius_def, pow_succ, pow_mul]

end Series

section OneVar

variable {k : Type v} [Field k] [CharP k p]

abbrev T : MvPowerSeries (Fin 1) k := X 0

theorem fin1_fun_eq {α : Type*} (f : Fin 1 → α) : f = fun _ => f 0 := by
  funext i; rw [Fin.fin_one_eq_zero i]

theorem hasSubst_const {τ : Type*} {x : MvPowerSeries τ k} (hx : constantCoeff x = 0) :
    HasSubst (fun _ : Fin 1 => x) :=
  hasSubst_of_constantCoeff_zero fun _ => hx

theorem subst_self_fin1 (f : MvPowerSeries (Fin 1) k) :
    subst (fun _ : Fin 1 => (T : MvPowerSeries (Fin 1) k)) f = f := by
  have h := congrFun (MvPowerSeries.subst_self (σ := Fin 1) (R := k)) f
  rw [fin1_fun_eq X] at h
  exact h

theorem expand_eq_subst {n : ℕ} (hn : n ≠ 0) (f : MvPowerSeries (Fin 1) k) :
    expand n hn f = subst (fun _ : Fin 1 => (T : MvPowerSeries (Fin 1) k) ^ n) f := by
  rw [expand, coe_substAlgHom]
  congr 1
  exact fin1_fun_eq _

theorem constantCoeff_T_pow {n : ℕ} (hn : n ≠ 0) :
    constantCoeff ((T : MvPowerSeries (Fin 1) k) ^ n) = 0 := by
  rw [map_pow, constantCoeff_X, zero_pow hn]

theorem subst_const_T_pow {τ : Type*} {x : MvPowerSeries τ k} (hx : constantCoeff x = 0) (n : ℕ) :
    subst (fun _ : Fin 1 => x) ((T : MvPowerSeries (Fin 1) k) ^ n) = x ^ n := by
  rw [subst_pow (hasSubst_const hx), subst_X (hasSubst_const hx)]

theorem subst_const_expand {τ : Type*} {x : MvPowerSeries τ k} (hx : constantCoeff x = 0) {n : ℕ}
    (hn : n ≠ 0) (f : MvPowerSeries (Fin 1) k) :
    subst (fun _ : Fin 1 => x) (expand n hn f) = subst (fun _ : Fin 1 => x ^ n) f := by
  rw [expand_eq_subst, subst_comp_subst_apply (hasSubst_const (constantCoeff_T_pow hn))
    (hasSubst_const hx)]
  congr 1
  funext s
  exact subst_const_T_pow hx n

theorem subst_expand_const {g : MvPowerSeries (Fin 1) k} (hg : constantCoeff g = 0) {n : ℕ}
    (hn : n ≠ 0) (x : MvPowerSeries (Fin 1) k) :
    subst (fun _ : Fin 1 => expand n hn g) x = expand n hn (subst (fun _ : Fin 1 => g) x) := by
  rw [expand_eq_subst hn (subst _ x), subst_comp_subst_apply (hasSubst_const hg)
    (hasSubst_const (constantCoeff_T_pow hn))]
  congr 1
  funext s
  exact expand_eq_subst hn g

theorem constantCoeff_expand' {n : ℕ} (hn : n ≠ 0) (f : MvPowerSeries (Fin 1) k) :
    constantCoeff (expand n hn f) = constantCoeff f :=
  constantCoeff_expand n hn f

theorem coeff_one_subst_const {x : MvPowerSeries (Fin 1) k} (hx : constantCoeff x = 0)
    (f : MvPowerSeries (Fin 1) k) :
    coeff (Finsupp.single 0 1) (subst (fun _ : Fin 1 => x) f) =
      coeff (Finsupp.single 0 1) f * coeff (Finsupp.single 0 1) x := by
  rw [MvFormalGroup.coeff_single_subst (fun _ => hx)]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]

theorem coeff_pow_eq_zero_of_lt {x : MvPowerSeries (Fin 1) k} (hx : constantCoeff x = 0)
    {N : ℕ} {m : Fin 1 →₀ ℕ} (hm : m 0 < N) : coeff m (x ^ N) = 0 := by
  have hdvd : (T : MvPowerSeries (Fin 1) k) ∣ x := by
    rw [X_dvd_iff]
    intro m' hm'
    have : m' = 0 := by
      rw [Finsupp.unique_single m']
      simp only [Fin.default_eq_zero, Fin.isValue, hm', Finsupp.single_zero]
    rw [this, coeff_zero_eq_constantCoeff_apply, hx]
  have hdvd' : (T : MvPowerSeries (Fin 1) k) ^ N ∣ x ^ N := pow_dvd_pow_of_dvd hdvd N
  exact (X_pow_dvd_iff.mp hdvd') m hm

end OneVar

section Main

variable {κ : Type u} [Field κ] [Fintype κ] [CharP κ p]
variable {k : Type v} [Field k] [CharP k p]
variable (j : WittVector p κ →+* k)
variable (G : MvFormalGroup 1 k) [G.IsComm]
variable (ρ : WittVector p κ →+* MvFormalGroup.End G)

local notation "𝕎" => WittVector p κ
local notation "q" => Fintype.card κ

abbrev ser (e : MvFormalGroup.End G) : MvPowerSeries (Fin 1) k := MvFormalGroup.Hom.toPowerSeries e 0

theorem toPowerSeries_eq (e : MvFormalGroup.End G) :
    MvFormalGroup.Hom.toPowerSeries e = fun _ => ser G e :=
  fin1_fun_eq _

theorem constantCoeff_ser (e : MvFormalGroup.End G) : constantCoeff (ser G e) = 0 :=
  MvFormalGroup.Hom.constantCoeff_eq_zero e 0

theorem hasSubst_ser (e : MvFormalGroup.End G) : HasSubst (fun _ : Fin 1 => ser G e) :=
  hasSubst_const (constantCoeff_ser G e)

theorem ser_mul (e e' : MvFormalGroup.End G) :
    ser G (e * e') = subst (fun _ : Fin 1 => ser G e') (ser G e) := by
  show subst (MvFormalGroup.Hom.toPowerSeries e') (ser G e) = _
  rw [toPowerSeries_eq G e']

theorem ext_ser {e e' : MvFormalGroup.End G} (h : ser G e = ser G e') : e = e' := by
  apply MvFormalGroup.Hom.ext
  rw [toPowerSeries_eq G e, toPowerSeries_eq G e', h]

def D (e : MvFormalGroup.End G) : k := coeff (Finsupp.single 0 1) (ser G e)

theorem D_eq_linearPartHom (e : MvFormalGroup.End G) : D G e = MvFormalGroup.linearPartHom G e 0 0 := rfl

theorem D_add (e e' : MvFormalGroup.End G) : D G (e + e') = D G e + D G e' := by
  rw [D_eq_linearPartHom, map_add, Matrix.add_apply, ← D_eq_linearPartHom, ← D_eq_linearPartHom]

theorem D_sub (e e' : MvFormalGroup.End G) : D G (e - e') = D G e - D G e' := by
  rw [D_eq_linearPartHom, map_sub, Matrix.sub_apply, ← D_eq_linearPartHom, ← D_eq_linearPartHom]

theorem D_mul (e e' : MvFormalGroup.End G) : D G (e * e') = D G e * D G e' := by
  show coeff _ (ser G (e * e')) = _
  rw [ser_mul, coeff_one_subst_const (constantCoeff_ser G e')]
  rfl

variable (p κ) in

def ff : ℕ := ((FiniteField.card κ p).choose : ℕ+)

local notation "𝔣" => ff p κ

theorem card_eq : q = p ^ 𝔣 := (FiniteField.card κ p).choose_spec.2

theorem ff_pos : 0 < 𝔣 := PNat.pos _

private theorem _root_.P2mKcCommutantLT.one_lt_card : 1 < q := Fintype.one_lt_card

p2m_export "P2mKcCommutantLT" "one_lt_card"

theorem exists_pow_ne {n : ℕ} (hn0 : 0 < n) (hn : p ^ n < q) : ∃ x : κ, x ^ p ^ n ≠ x := by
  classical
  by_contra h
  push Not at h
  have hp1 : 1 < p ^ n := Nat.one_lt_pow hn0.ne' (Fact.out : p.Prime).one_lt
  set P : Polynomial κ := Polynomial.X ^ p ^ n - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hdeg : P.natDegree = p ^ n := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1
  have hroots : ∀ x : κ, x ∈ P.roots := by
    intro x
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h x, sub_self]
  have hcard : q ≤ p ^ n := by
    calc q = (Finset.univ : Finset κ).card := Finset.card_univ.symm
      _ ≤ P.roots.toFinset.card :=
          Finset.card_le_card fun x _ => Multiset.mem_toFinset.mpr (hroots x)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p ^ n := hdeg
  omega

theorem j_eq_zero_iff (c : 𝕎) : j c = 0 ↔ c.coeff 0 = 0 := by
  constructor
  · intro hc
    by_contra h0
    have hu : IsUnit (j c) := (WittVector.isUnit_of_coeff_zero_ne_zero c h0).map j
    exact hu.ne_zero hc
  · intro h0
    have hmem : c ∈ Ideal.span {(p : 𝕎)} := (WittVector.mem_span_p_iff_coeff_zero_eq_zero c).mpr h0
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← hd, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]

theorem j_teichmuller_injective :
    Function.Injective fun x : κ => j (WittVector.teichmuller p x) := by
  intro x y hxy
  have h0 : j (WittVector.teichmuller p x - WittVector.teichmuller p y) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hxy
  rw [j_eq_zero_iff, ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero] at h0
  exact sub_eq_zero.mp h0

theorem j_teichmuller_pow (x : κ) (n : ℕ) :
    j (WittVector.teichmuller p x) ^ n = j (WittVector.teichmuller p (x ^ n)) := by
  rw [← map_pow, ← map_pow]

theorem exists_teichmuller_of_pow_card_eq (y : k) (hy : y ^ q = y) :
    ∃ x : κ, j (WittVector.teichmuller p x) = y := by
  classical
  set P : Polynomial k := Polynomial.X ^ q - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ one_lt_card
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq _ one_lt_card
  set R : Finset k := P.roots.toFinset with hR
  set I : Finset k := Finset.univ.image fun x : κ => j (WittVector.teichmuller p x) with hI
  have hmemR : ∀ z : k, z ∈ R ↔ z ^ q = z := by
    intro z
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have hIR : I ⊆ R := by
    intro z hz
    rw [hI, Finset.mem_image] at hz
    obtain ⟨x, -, rfl⟩ := hz
    rw [hmemR, j_teichmuller_pow, FiniteField.pow_card]
  have hcardI : I.card = q := by
    rw [hI, Finset.card_image_of_injective _ (j_teichmuller_injective j), Finset.card_univ]
  have hcardR : R.card ≤ q := by
    calc R.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hdeg
  have hIeqR : I = R := Finset.eq_of_subset_of_card_le hIR (hcardI ▸ hcardR)
  have hy' : y ∈ I := by rw [hIeqR, hmemR]; exact hy
  rw [hI, Finset.mem_image] at hy'
  obtain ⟨x, -, hx⟩ := hy'
  exact ⟨x, hx⟩

def Fr (n : ℕ) : MvFormalGroup 1 k := G.map (iterateFrobenius k p n)

theorem Fr_toPowerSeries (n : ℕ) (i : Fin 1) :
    (Fr G n).toPowerSeries i = map (iterateFrobenius k p n) (G.toPowerSeries i) := rfl

def blocks (g : MvPowerSeries (Fin 1) k) : Fin 1 ⊕ Fin 1 → MvPowerSeries (Fin 1 ⊕ Fin 1) k :=
  Sum.elim (fun _ => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k)) g)
    (fun _ => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k)) g)

theorem hasSubst_Xinl :
    HasSubst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_Xinr :
    HasSubst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blocks {g : MvPowerSeries (Fin 1) k} (hg : constantCoeff g = 0)
    (s : Fin 1 ⊕ Fin 1) : constantCoeff (blocks g s) = 0 := by
  rcases s with l | l
  · exact constantCoeff_subst_eq_zero hasSubst_Xinl (fun _ => constantCoeff_X _) hg
  · exact constantCoeff_subst_eq_zero hasSubst_Xinr (fun _ => constantCoeff_X _) hg

theorem hasSubst_blocks {g : MvPowerSeries (Fin 1) k} (hg : constantCoeff g = 0) :
    HasSubst (blocks g) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blocks hg)

theorem blocks_expand {g : MvPowerSeries (Fin 1) k} (hg : constantCoeff g = 0) {n : ℕ} (hn : n ≠ 0) :
    blocks (expand n hn g) = fun s => expand n hn (blocks g s) := by
  funext s
  rcases s with l | l
  · show subst _ (expand n hn g) = expand n hn (subst _ g)
    rw [expand_subst n hn hasSubst_Xinl, expand, coe_substAlgHom,
      subst_comp_subst_apply (HasSubst.X_pow hn) hasSubst_Xinl]
    congr 1
    funext i
    rw [subst_pow hasSubst_Xinl, subst_X hasSubst_Xinl, expand_X]
  · show subst _ (expand n hn g) = expand n hn (subst _ g)
    rw [expand_subst n hn hasSubst_Xinr, expand, coe_substAlgHom,
      subst_comp_subst_apply (HasSubst.X_pow hn) hasSubst_Xinr]
    congr 1
    funext i
    rw [subst_pow hasSubst_Xinr, subst_X hasSubst_Xinr, expand_X]

structure Good (n : ℕ) (g : MvPowerSeries (Fin 1) k) : Prop where
  const : constantCoeff g = 0
  hom : subst (Fr G n).toPowerSeries g = subst (blocks g) (G.toPowerSeries 0)
  comm : ∀ a : 𝕎, subst (fun _ : Fin 1 => map (iterateFrobenius k p n) (ser G (ρ a))) g =
    subst (fun _ : Fin 1 => g) (ser G (ρ a))

def mkEnd (g : MvPowerSeries (Fin 1) k) (hg0 : constantCoeff g = 0)
    (hhom : subst G.toPowerSeries g = subst (blocks g) (G.toPowerSeries 0)) : MvFormalGroup.End G :=
  ⟨fun _ => g, fun _ => hg0, fun i => by rw [Fin.fin_one_eq_zero i]; exact hhom⟩

@[scoped simp] theorem ser_mkEnd (g : MvPowerSeries (Fin 1) k) (hg0 : constantCoeff g = 0)
    (hhom : subst G.toPowerSeries g = subst (blocks g) (G.toPowerSeries 0)) :
    ser G (mkEnd G g hg0 hhom) = g := rfl

structure Hyp : Prop where
  h1 : ∀ a, coeff (Finsupp.single 0 1) (ser G (ρ a)) = j a
  hp : ser G (ρ (p : 𝕎)) = T ^ q

variable {j G ρ}

theorem ser_rho_p (H : Hyp j G ρ) : ser G (ρ (p : 𝕎)) = T ^ p ^ 𝔣 := by
  rw [H.hp, card_eq]

theorem D_rho (H : Hyp j G ρ) (a : 𝕎) : D G (ρ a) = j a := H.h1 a

theorem ser_mul_rho_p (H : Hyp j G ρ) (e : MvFormalGroup.End G) :
    ser G (e * ρ (p : 𝕎)) = expand (p ^ 𝔣) (hpn0 _) (ser G e) := by
  rw [ser_mul, ser_rho_p H, expand_eq_subst]

theorem ser_rho_p_mul (H : Hyp j G ρ) (e : MvFormalGroup.End G) :
    ser G (ρ (p : 𝕎) * e) = ser G e ^ p ^ 𝔣 := by
  rw [ser_mul, ser_rho_p H, subst_const_T_pow (constantCoeff_ser G e)]

theorem map_iterateFrobenius_ser (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : e * ρ (p : 𝕎) = ρ (p : 𝕎) * e) :
    map (iterateFrobenius k p 𝔣) (ser G e) = ser G e := by
  have h := congrArg (ser G) he
  rw [ser_mul_rho_p H, ser_rho_p_mul H, pow_pow_eq_expand_map] at h
  exact (expand_injective _ h).symm

theorem map_iterateFrobenius_rho (H : Hyp j G ρ) (a : 𝕎) :
    map (iterateFrobenius k p 𝔣) (ser G (ρ a)) = ser G (ρ a) :=
  map_iterateFrobenius_ser H (by rw [← map_mul, ← map_mul, mul_comm])

theorem map_iterateFrobenius_law (H : Hyp j G ρ) (i : Fin 1) :
    map (iterateFrobenius k p 𝔣) (G.toPowerSeries i) = G.toPowerSeries i := by
  rw [Fin.fin_one_eq_zero i]
  have key := MvFormalGroup.Hom.subst_eq (ρ (p : 𝕎)) 0
  rw [toPowerSeries_eq G, ser_rho_p H, subst_pow G.hasSubst_toPowerSeries,
    subst_X G.hasSubst_toPowerSeries] at key
  have hfam : (Sum.elim
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k))
        ((T : MvPowerSeries (Fin 1) k) ^ p ^ 𝔣))
      (fun _ : Fin 1 => subst (fun l : Fin 1 => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) k))
        ((T : MvPowerSeries (Fin 1) k) ^ p ^ 𝔣)))
      = fun s : Fin 1 ⊕ Fin 1 => (X s : MvPowerSeries (Fin 1 ⊕ Fin 1) k) ^ p ^ 𝔣 := by
    funext s
    rcases s with l | l
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inl,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inr,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  rw [hfam] at key
  have key' : G.toPowerSeries 0 ^ p ^ 𝔣 = expand (p ^ 𝔣) (hpn0 _) (G.toPowerSeries 0) := by
    rw [key, expand, coe_substAlgHom]
  rw [pow_pow_eq_expand_map] at key'
  exact expand_injective _ key'

theorem law_map_iterateFrobenius (H : Hyp j G ρ) : G.map (iterateFrobenius k p 𝔣) = G :=
  MvFormalGroup.ext (funext fun i => map_iterateFrobenius_law H i)

theorem D_pow_card (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : e * ρ (p : 𝕎) = ρ (p : 𝕎) * e) :
    D G e ^ q = D G e := by
  have h := congrArg (coeff (Finsupp.single 0 1)) (map_iterateFrobenius_ser H he)
  rw [coeff_map, iterateFrobenius_def, ← card_eq] at h
  exact h

theorem exists_D_eq (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) :
    ∃ x : κ, D G (ρ (WittVector.teichmuller p x)) = D G e := by
  obtain ⟨x, hx⟩ := exists_teichmuller_of_pow_card_eq j (D G e) (D_pow_card H (he _))
  exact ⟨x, by rw [D_rho H, hx]⟩

theorem good_zero {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) : Good G ρ 0 (ser G e) := by
  have hFr0 : (Fr G 0).toPowerSeries = G.toPowerSeries := by
    funext i
    rw [Fr_toPowerSeries, iterateFrobenius_zero, MvPowerSeries.map_id]
    rfl
  refine ⟨constantCoeff_ser G e, ?_, fun a => ?_⟩
  · rw [hFr0]
    have := MvFormalGroup.Hom.subst_eq e 0
    rw [toPowerSeries_eq G e] at this
    exact this
  · rw [iterateFrobenius_zero, MvPowerSeries.map_id]
    have := congrArg (ser G) (he a)
    rw [ser_mul, ser_mul] at this
    exact this

theorem step (n : ℕ) {g : MvPowerSeries (Fin 1) k} (hg : Good G ρ n g)
    (hD : coeff (Finsupp.single 0 1) g = 0) :
    ∃ g' : MvPowerSeries (Fin 1) k, Good G ρ (n + 1) g' ∧ g = expand p hp0 g' := by
  classical

  have hvan : ∀ m : Fin 1 →₀ ℕ, ¬ p ∣ m 0 → coeff m g = 0 := by
    intro m hm
    refine MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p (Fr G n) G
      (fun _ => g) (fun _ => hg.const) ?_ (fun i => ?_) 0 m ⟨0, hm⟩
    · ext i i'
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero i']
      simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.zero_apply]
      exact hD
    · rw [Fin.fin_one_eq_zero i]
      exact hg.hom

  let g' : MvPowerSeries (Fin 1) k := fun m => coeff (p • m) g
  have hgg' : expand p hp0 g' = g := by
    ext m
    by_cases hdvd : p ∣ m 0
    · obtain ⟨c, hc⟩ := hdvd
      have hm : m = p • Finsupp.single 0 c := by
        rw [Finsupp.unique_single m]
        ext
        simp only [Fin.default_eq_zero, Fin.isValue, Finsupp.single_eq_same, Finsupp.coe_smul,
          Pi.smul_apply, smul_eq_mul, hc]
      rw [hm, coeff_expand_smul]
      rfl
    · rw [coeff_expand_of_not_dvd p hp0 g' hdvd, hvan m hdvd]
  have hconst' : constantCoeff g' = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    show coeff (p • (0 : Fin 1 →₀ ℕ)) g = 0
    rw [smul_zero, coeff_zero_eq_constantCoeff_apply, hg.const]
  refine ⟨g', ⟨hconst', ?_, fun a => ?_⟩, hgg'.symm⟩
  ·
    have hh := hg.hom
    rw [← hgg'] at hh

    have hL : subst (Fr G n).toPowerSeries (expand p hp0 g') =
        expand p hp0 (subst (Fr G (n + 1)).toPowerSeries g') := by
      rw [expand, coe_substAlgHom, subst_comp_subst_apply (HasSubst.X_pow hp0)
        (Fr G n).hasSubst_toPowerSeries, expand_subst p hp0 (Fr G (n + 1)).hasSubst_toPowerSeries]
      congr 1
      funext s
      rw [subst_pow (Fr G n).hasSubst_toPowerSeries, subst_X (Fr G n).hasSubst_toPowerSeries,
        Fr_toPowerSeries, Fr_toPowerSeries, pow_p_eq_expand_map, map_frobenius_map_iterateFrobenius]

    have hR : subst (blocks (expand p hp0 g')) (G.toPowerSeries 0) =
        expand p hp0 (subst (blocks g') (G.toPowerSeries 0)) := by
      rw [blocks_expand hconst', expand_subst p hp0 (hasSubst_blocks hconst')]
    rw [hL, hR] at hh
    exact expand_injective _ hh
  ·
    have hc := hg.comm a
    rw [← hgg'] at hc
    have hr0 : constantCoeff (ser G (ρ a)) = 0 := constantCoeff_ser G _
    have hrn0 : ∀ m : ℕ, constantCoeff (map (iterateFrobenius k p m) (ser G (ρ a))) = 0 := by
      intro m; rw [constantCoeff_map, hr0, map_zero]
    have hL : subst (fun _ : Fin 1 => map (iterateFrobenius k p n) (ser G (ρ a))) (expand p hp0 g') =
        expand p hp0 (subst (fun _ : Fin 1 => map (iterateFrobenius k p (n + 1)) (ser G (ρ a))) g') := by
      rw [subst_const_expand (hrn0 n), pow_p_eq_expand_map, map_frobenius_map_iterateFrobenius,
        expand_subst p hp0 (hasSubst_const (hrn0 (n + 1)))]
    have hR : subst (fun _ : Fin 1 => expand p hp0 g') (ser G (ρ a)) =
        expand p hp0 (subst (fun _ : Fin 1 => g') (ser G (ρ a))) :=
      subst_expand_const hconst' hp0 _
    rw [hL, hR] at hc
    exact expand_injective _ hc

theorem coeff_one_eq_zero_of_good (H : Hyp j G ρ) {n : ℕ} (hn0 : 0 < n) (hn : n < 𝔣) {g : MvPowerSeries (Fin 1) k}
    (hg : Good G ρ n g) : coeff (Finsupp.single 0 1) g = 0 := by
  have hlt : p ^ n < q := by
    rw [card_eq]; exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hn
  obtain ⟨x, hx⟩ := exists_pow_ne (p := p) (κ := κ) hn0 hlt
  set a : 𝕎 := WittVector.teichmuller p x with ha
  have hr0 : constantCoeff (ser G (ρ a)) = 0 := constantCoeff_ser G _
  have hrn0 : constantCoeff (map (iterateFrobenius k p n) (ser G (ρ a))) = 0 := by
    rw [constantCoeff_map, hr0, map_zero]
  have hc := congrArg (coeff (Finsupp.single 0 1)) (hg.comm a)
  rw [coeff_one_subst_const hrn0, coeff_one_subst_const hg.const, coeff_map, iterateFrobenius_def]
    at hc
  have h1 : coeff (Finsupp.single 0 1) (ser G (ρ a)) = j a := H.h1 a
  rw [h1] at hc

  have hne : j a ^ p ^ n ≠ j a := by
    rw [ha, j_teichmuller_pow]
    intro heq
    exact hx (j_teichmuller_injective j heq)
  have : coeff (Finsupp.single 0 1) g * (j a ^ p ^ n - j a) = 0 := by
    rw [mul_sub, hc, mul_comm, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

theorem descend (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) (hD : D G e = 0) :
    ∀ n : ℕ, n ≤ 𝔣 → ∃ g, Good G ρ n g ∧ ser G e = expand (p ^ n) (hpn0 n) g := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨ser G e, good_zero he, ?_⟩
    rw [expand_eq_subst, pow_zero, pow_one]
    exact (subst_self_fin1 (ser G e)).symm
  | succ n ih =>
    intro hn
    obtain ⟨g, hg, hge⟩ := ih (Nat.le_of_succ_le hn)
    have hDg : coeff (Finsupp.single 0 1) g = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have : g = ser G e := by
          rw [hge, expand_eq_subst, pow_zero, pow_one, subst_self_fin1]
        rw [this]; exact hD
      · exact coeff_one_eq_zero_of_good H hpos (Nat.lt_of_succ_le hn) hg
    obtain ⟨g', hg', hgg'⟩ := step n hg hDg
    refine ⟨g', hg', ?_⟩
    rw [hge, hgg']
    exact (expand_mul (p ^ n) (hpn0 n) p hp0 g').symm

theorem exists_eq_rho_p_mul (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) (hD : D G e = 0) :
    ∃ h : MvFormalGroup.End G, (∀ a, h * ρ a = ρ a * h) ∧ e = ρ (p : 𝕎) * h := by
  obtain ⟨g, hg, hge⟩ := descend H he hD 𝔣 le_rfl
  have hhom : subst G.toPowerSeries g = subst (blocks g) (G.toPowerSeries 0) := by
    have := hg.hom
    rwa [show Fr G 𝔣 = G from law_map_iterateFrobenius H] at this
  set h : MvFormalGroup.End G := mkEnd G g hg.const hhom with hh
  have hC : ∀ a, h * ρ a = ρ a * h := by
    intro a
    apply ext_ser G
    rw [ser_mul, ser_mul, ser_mkEnd]
    have := hg.comm a
    rwa [map_iterateFrobenius_rho H a] at this
  refine ⟨h, hC, ?_⟩
  rw [← hC (p : 𝕎)]
  apply ext_ser G
  rw [ser_mul_rho_p H, ser_mkEnd, hge]

theorem exists_digit (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) :
    ∃ (x : κ) (h : MvFormalGroup.End G), (∀ a, h * ρ a = ρ a * h) ∧
      e = ρ (WittVector.teichmuller p x) + ρ (p : 𝕎) * h := by
  obtain ⟨x, hx⟩ := exists_D_eq H he
  set e' := e - ρ (WittVector.teichmuller p x) with he'
  have hC' : ∀ a, e' * ρ a = ρ a * e' := by
    intro a
    rw [he', sub_mul, mul_sub, he a, ← map_mul, ← map_mul, mul_comm]
  have hD' : D G e' = 0 := by rw [he', D_sub, hx, sub_self]
  obtain ⟨h, hh, hh'⟩ := exists_eq_rho_p_mul H hC' hD'
  exact ⟨x, h, hh, by rw [← hh', he', add_sub_cancel]⟩

structure CSt (ρ : 𝕎 →+* MvFormalGroup.End G) where

  e : MvFormalGroup.End G

  isC : ∀ a, e * ρ a = ρ a * e

def nxt (H : Hyp j G ρ) (s : CSt ρ) : κ × CSt ρ :=
  ⟨(exists_digit H s.isC).choose,
    ⟨(exists_digit H s.isC).choose_spec.choose, (exists_digit H s.isC).choose_spec.choose_spec.1⟩⟩

theorem nxt_spec (H : Hyp j G ρ) (s : CSt ρ) :
    s.e = ρ (WittVector.teichmuller p (nxt H s).1) + ρ (p : 𝕎) * (nxt H s).2.e :=
  (exists_digit H s.isC).choose_spec.choose_spec.2

def sq (H : Hyp j G ρ) (s : CSt ρ) : ℕ → CSt ρ
  | 0 => s
  | n + 1 => (nxt H (sq H s n)).2

def dg (H : Hyp j G ρ) (s : CSt ρ) (n : ℕ) : κ := (nxt H (sq H s n)).1

def ps (H : Hyp j G ρ) (s : CSt ρ) (n : ℕ) : 𝕎 :=
  ∑ i ∈ Finset.range n, WittVector.teichmuller p (dg H s i) * (p : 𝕎) ^ i

theorem decomp (H : Hyp j G ρ) (s : CSt ρ) (n : ℕ) :
    s.e = ρ (ps H s n) + ρ (p : 𝕎) ^ n * (sq H s n).e := by
  induction n with
  | zero => simp [ps, sq]
  | succ n ih =>
    have hps : ps H s (n + 1) = ps H s n + WittVector.teichmuller p (dg H s n) * (p : 𝕎) ^ n :=
      Finset.sum_range_succ _ _
    have hsq : sq H s (n + 1) = (nxt H (sq H s n)).2 := rfl
    have hdg : dg H s n = (nxt H (sq H s n)).1 := rfl
    rw [ih, hps, hsq, hdg, map_add, add_assoc, nxt_spec H (sq H s n), mul_add, ← mul_assoc,
      ← pow_succ, ← map_pow, ← map_mul, mul_comm ((p : 𝕎) ^ n)]

theorem ps_sub_mem (H : Hyp j G ρ) (s : CSt ρ) {m n : ℕ} (hmn : m ≤ n) :
    ps H s n - ps H s m ∈ Ideal.span {((p : 𝕎) ^ m)} := by
  induction n, hmn using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    rw [ps, Finset.sum_range_succ, ← ps, add_sub_right_comm]
    refine Ideal.add_mem _ ih (Ideal.mem_span_singleton.mpr ?_)
    exact Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _

theorem exists_limit (H : Hyp j G ρ) (s : CSt ρ) :
    ∃ a : 𝕎, ∀ n, ps H s n - a ∈ Ideal.span {((p : 𝕎) ^ n)} := by
  have hI : ∀ n : ℕ, (Ideal.span {(p : 𝕎)} ^ n • ⊤ : Submodule 𝕎 𝕎) = Ideal.span {((p : 𝕎) ^ n)} := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : 𝕎)}) (M := 𝕎) (ps H s) (by
    intro m n hmn
    rw [SModEq.sub_mem, hI]
    have := ps_sub_mem H s hmn
    rwa [← neg_sub, Ideal.neg_mem_iff])
  refine ⟨a, fun n => ?_⟩
  have := ha n
  rwa [SModEq.sub_mem, hI] at this

theorem ser_rho_p_pow (H : Hyp j G ρ) (n : ℕ) : ser G (ρ (p : 𝕎) ^ n) = T ^ (p ^ 𝔣) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ, ser_mul, ser_rho_p H, ih, subst_const_T_pow (constantCoeff_T_pow (hpn0 _)),
      ← pow_mul, ← pow_succ']

theorem coeff_ser_rho_p_pow_mul (H : Hyp j G ρ) (n : ℕ) (y : MvFormalGroup.End G)
    {m : Fin 1 →₀ ℕ} (hm : m 0 < (p ^ 𝔣) ^ n) : coeff m (ser G (ρ (p : 𝕎) ^ n * y)) = 0 := by
  rw [ser_mul, ser_rho_p_pow H, subst_const_T_pow (constantCoeff_ser G y)]
  exact coeff_pow_eq_zero_of_lt (constantCoeff_ser G y) hm

theorem exists_eq_rho (H : Hyp j G ρ) {e : MvFormalGroup.End G} (he : ∀ a, e * ρ a = ρ a * e) :
    ∃ a : 𝕎, e = ρ a := by
  set s : CSt ρ := ⟨e, he⟩ with hs
  obtain ⟨a, ha⟩ := exists_limit H s
  refine ⟨a, ?_⟩
  have key : ∀ n, ∃ y : MvFormalGroup.End G, e - ρ a = ρ (p : 𝕎) ^ n * y := by
    intro n
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (ha n)
    refine ⟨ρ c + (sq H s n).e, ?_⟩
    have hd := decomp H s n
    change e = _ at hd
    rw [mul_add, ← map_pow, ← map_mul, ← hc, map_sub, map_pow, hd]
    abel
  apply ext_ser G

  have hzero : ser G (e - ρ a) = 0 := by
    ext m
    obtain ⟨y, hy⟩ := key (m 0 + 1)
    rw [hy, LinearMap.map_zero]
    have h2 : 2 ≤ p ^ 𝔣 := by rw [← card_eq]; exact one_lt_card
    have hm : m 0 < (p ^ 𝔣) ^ (m 0 + 1) :=
      calc m 0 < 2 ^ (m 0) := Nat.lt_two_pow_self
        _ ≤ (p ^ 𝔣) ^ (m 0) := Nat.pow_le_pow_left h2 _
        _ ≤ (p ^ 𝔣) ^ (m 0 + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
    exact coeff_ser_rho_p_pow_mul H _ y hm
  have : e - ρ a = 0 := by
    apply ext_ser G
    rw [hzero]; rfl
  rw [sub_eq_zero.mp this]

theorem rho_injective (H : Hyp j G ρ) : Function.Injective ρ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have key : ∀ n : ℕ, ∀ c : 𝕎, ρ c = 0 → c ∈ Ideal.span {((p : 𝕎) ^ n)} := by
    intro n
    induction n with
    | zero => intro c _; rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
    | succ n ih =>
      intro c hc

      have hj : j c = 0 := by rw [← D_rho H c, hc]; rfl
      have h0 : c.coeff 0 = 0 := (j_eq_zero_iff j c).mp hj
      obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).mpr h0)

      have hρc' : ρ c' = 0 := by
        have h1 : ρ (p : 𝕎) * ρ c' = 0 := by rw [← map_mul, ← hc', hc]
        have h2 := congrArg (ser G) h1
        rw [ser_rho_p_mul H] at h2
        have h3 : ser G (ρ c') = 0 := pow_eq_zero_iff (hpn0 _) |>.mp h2
        apply ext_ser G
        rw [h3]; rfl
      rw [hc', pow_succ']
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (ih c' hρc') |>
        (Ideal.span_singleton_mul_span_singleton _ _).le
  apply IsHausdorff.haus' (I := Ideal.span {(p : 𝕎)}) (M := 𝕎) c
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact key n c hc

end Main

end P2mKcCommutantLT
p2m_reactivate "P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.P2mKcCommutantLT"

end
p2m_reactivate "P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.P2mKcCommutantLT"

open P2mKcCommutantLT in

theorem solution
    (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [Fintype κ] [CharP κ p]
    {k : Type v} [Field k] [CharP k p] (j : WittVector p κ →+* k)
    (G : MvFormalGroup 1 k) [G.IsComm] (ρ : WittVector p κ →+* MvFormalGroup.End G)
    (hρ1 : ∀ a, MvPowerSeries.coeff (Finsupp.single 0 1) ((ρ a).toPowerSeries 0) = j a)
    (hρp : (ρ (p : WittVector p κ)).toPowerSeries 0 =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) k) ^ Fintype.card κ) :
    Function.Injective ρ ∧
      ∀ e : MvFormalGroup.End G, (∀ a, e * ρ a = ρ a * e) → ∃ a, e = ρ a :=
  have H : Hyp j G ρ := ⟨hρ1, hρp⟩
  ⟨rho_injective H, fun _ he => exists_eq_rho H he⟩

end S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
end P2MW
export P2MW.S_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card (solution)
