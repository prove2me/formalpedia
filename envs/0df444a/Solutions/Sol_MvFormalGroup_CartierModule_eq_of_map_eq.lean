-- Prove2me | solution 1 for MvFormalGroup.CartierModule.eq_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cbd50258-bf49-5619-82a2-9f3c71257273

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mKcCartierFaithful

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

def contract (n : ℕ) {σ : Type*} (F : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun e => coeff (n • e) F

omit hp in
theorem coeff_contract (n : ℕ) {σ : Type*} (F : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    coeff e (contract n F) = coeff (n • e) F := rfl

theorem expand_contract {σ : Type*} (F : MvPowerSeries σ R)
    (hF : ∀ e : σ →₀ ℕ, (∃ i, ¬ p ∣ e i) → coeff e F = 0) :
    expand p hp.out.ne_zero (contract p F) = F := by
  ext e
  by_cases h : ∀ i, p ∣ e i
  · obtain ⟨m, rfl⟩ : ∃ m : σ →₀ ℕ, p • m = e :=
      ⟨e.mapRange (fun a => a / p) (by simp), by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [coeff_expand_smul, coeff_contract]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp.out.ne_zero _ hi, hF e ⟨i, hi⟩]

omit hp in
theorem constantCoeff_contract (n : ℕ) {σ : Type*} (F : MvPowerSeries σ R)
    (hF : F.constantCoeff = 0) : (contract n F).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_contract, smul_zero,
    coeff_zero_eq_constantCoeff_apply, hF]

omit hp in

theorem expand_injective {σ : Type*} (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (expand n hn : MvPowerSeries σ R → MvPowerSeries σ R) := by
  intro F G h
  ext e
  have := congrArg (coeff (n • e)) h
  rwa [coeff_expand_smul, coeff_expand_smul] at this

omit hp in

theorem subst_expand {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (n : ℕ)
    (hn : n ≠ 0) (g : MvPowerSeries σ R) :
    subst a (expand n hn g) = subst (fun s => a s ^ n) g := by
  rw [expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hn) ha]
  congr 1
  funext s
  rw [subst_pow ha, subst_X ha]

omit hp in

theorem expand_subst_X_comp {σ τ : Type*} [Finite σ] (ι : σ → τ) (n : ℕ) (hn : n ≠ 0)
    (g : MvPowerSeries σ R) :
    expand n hn (subst (fun s => (X (ι s) : MvPowerSeries τ R)) g) =
      subst (fun s => (X (ι s) : MvPowerSeries τ R)) (expand n hn g) := by
  have hX : HasSubst (fun s => (X (ι s) : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  rw [MvPowerSeries.expand_subst n hn hX, subst_expand hX]
  congr 1
  funext s
  rw [expand_X]

theorem pow_eq_expand_map_frobenius [CharP R p] {σ : Type*} (g : MvPowerSeries σ R) :
    g ^ p = expand p hp.out.ne_zero (map (frobenius R p) g) := by
  rw [← map_expand, map_frobenius_expand]

theorem pow_eq_expand_map_iterateFrobenius [CharP R p] {σ : Type*} (g : MvPowerSeries σ R) (r : ℕ) :
    g ^ p ^ r = expand (p ^ r) (pow_ne_zero r hp.out.ne_zero) (map (iterateFrobenius R p r) g) := by
  rw [← map_expand, map_iterateFrobenius_expand p hp.out.ne_zero]

variable {d d' : ℕ}

def emb (θ : Fin d' → MvPowerSeries (Fin d) R) : Fin d' ⊕ Fin d' → MvPowerSeries (Fin d ⊕ Fin d) R :=
  Sum.elim
    (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))
    (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) (θ j))

def IsHomTuple (F : MvFormalGroup d R) (G : MvFormalGroup d' R)
    (θ : Fin d' → MvPowerSeries (Fin d) R) : Prop :=
  (∀ i, (θ i).constantCoeff = 0) ∧ ∀ i, subst F.toPowerSeries (θ i) = subst (emb θ) (G.toPowerSeries i)

omit hp in
theorem isHomTuple_hom {F : MvFormalGroup d R} {G : MvFormalGroup d' R} (φ : F.Hom G) :
    IsHomTuple F G φ.toPowerSeries :=
  ⟨φ.constantCoeff_eq_zero, φ.subst_eq⟩

omit hp in
theorem constantCoeff_emb {θ : Fin d' → MvPowerSeries (Fin d) R} (h0 : ∀ i, (θ i).constantCoeff = 0)
    (s : Fin d' ⊕ Fin d') : (emb θ s).constantCoeff = 0 := by
  rcases s with j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
      (fun l => constantCoeff_X _) (h0 j)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
      (fun l => constantCoeff_X _) (h0 j)

omit hp in
theorem hasSubst_emb {θ : Fin d' → MvPowerSeries (Fin d) R} (h0 : ∀ i, (θ i).constantCoeff = 0) :
    HasSubst (emb θ) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_emb h0)

omit hp in

theorem emb_expand (n : ℕ) (hn : n ≠ 0) (θ : Fin d' → MvPowerSeries (Fin d) R) :
    emb (fun i => expand n hn (θ i)) = fun s => expand n hn (emb θ s) := by
  funext s
  rcases s with j | j
  · exact (expand_subst_X_comp Sum.inl n hn (θ j)).symm
  · exact (expand_subst_X_comp Sum.inr n hn (θ j)).symm

theorem step [CharP R p] {F : MvFormalGroup d R} {G : MvFormalGroup d' R}
    {θ : Fin d' → MvPowerSeries (Fin d) R} (hθ : IsHomTuple F G θ)
    (hL : MvFormalGroup.linearPart θ = 0) :
    (∀ i, expand p hp.out.ne_zero (contract p (θ i)) = θ i) ∧
      IsHomTuple (F.map (frobenius R p)) G (fun i => contract p (θ i)) := by
  have hexp : ∀ i, expand p hp.out.ne_zero (contract p (θ i)) = θ i := fun i =>
    expand_contract (θ i) fun m hm =>
      MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p F G θ hθ.1 hL hθ.2 i m hm
  refine ⟨hexp, fun i => constantCoeff_contract p (θ i) (hθ.1 i), fun i => ?_⟩
  set θ' : Fin d' → MvPowerSeries (Fin d) R := fun i => contract p (θ i) with hθ'
  have h0' : ∀ i, (θ' i).constantCoeff = 0 := fun i => constantCoeff_contract p (θ i) (hθ.1 i)
  have hθexp : θ = fun i => expand p hp.out.ne_zero (θ' i) := funext fun i => (hexp i).symm
  apply expand_injective p hp.out.ne_zero

  have hFp : HasSubst (F.map (frobenius R p)).toPowerSeries := (F.map (frobenius R p)).hasSubst_toPowerSeries
  rw [MvPowerSeries.expand_subst p hp.out.ne_zero hFp]
  have hfam : (fun j => expand p hp.out.ne_zero ((F.map (frobenius R p)).toPowerSeries j)) =
      fun j => F.toPowerSeries j ^ p := by
    funext j
    exact (pow_eq_expand_map_frobenius (F.toPowerSeries j)).symm
  rw [hfam, ← subst_expand F.hasSubst_toPowerSeries p hp.out.ne_zero, hexp i, hθ.2 i, hθexp,
    emb_expand, ← MvPowerSeries.expand_subst p hp.out.ne_zero (hasSubst_emb h0')]

section Descent

variable [CharP R p] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def seq (δ : Φ.Hom Φ') : ℕ → Fin d' → MvPowerSeries (Fin d) R
  | 0 => δ.toPowerSeries
  | r + 1 => fun i => contract p (seq δ r i)

omit hp in
theorem map_map_law (f g : R →+* R) (F : MvFormalGroup d R) : (F.map f).map g = F.map (g.comp f) :=
  MvFormalGroup.ext (funext fun i => MvPowerSeries.map_map f g (F.toPowerSeries i))

omit hp in
theorem map_id_law (F : MvFormalGroup d R) : F.map (RingHom.id R) = F :=
  MvFormalGroup.ext (funext fun i => by
    show MvPowerSeries.map (RingHom.id R) (F.toPowerSeries i) = F.toPowerSeries i
    rw [MvPowerSeries.map_id]; rfl)

theorem iterateFrobenius_succ_eq (r : ℕ) :
    iterateFrobenius R p (r + 1) = (frobenius R p).comp (iterateFrobenius R p r) :=
  RingHom.ext fun x => by
    simp only [RingHom.comp_apply, iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

theorem inv_of_forall_lt (δ : Φ.Hom Φ') (r : ℕ)
    (hr : ∀ s, s < r → MvFormalGroup.linearPart (seq (p := p) δ s) = 0) :
    IsHomTuple (Φ.map (iterateFrobenius R p r)) Φ' (seq (p := p) δ r) ∧
      ∀ i, δ.toPowerSeries i =
        expand (p ^ r) (pow_ne_zero r hp.out.ne_zero) (seq (p := p) δ r i) := by
  induction r with
  | zero =>
    refine ⟨?_, fun i => ?_⟩
    · rw [iterateFrobenius_zero, map_id_law]
      exact isHomTuple_hom δ
    · have h1 : expand (σ := Fin d) (R := R) (p ^ 0) (pow_ne_zero 0 hp.out.ne_zero) =
          expand 1 one_ne_zero := by
        congr 1
      rw [h1, expand_one_apply]
      rfl
  | succ r ih =>
    obtain ⟨hHom, hExp⟩ := ih fun s hs => hr s (Nat.lt_succ_of_lt hs)
    obtain ⟨hexp, hHom'⟩ := step hHom (hr r (Nat.lt_succ_self r))
    refine ⟨?_, fun i => ?_⟩
    · rw [iterateFrobenius_succ_eq, ← map_map_law]
      exact hHom'
    · rw [hExp i, ← hexp i]
      show expand (p ^ r) _ (expand p _ (seq δ (r + 1) i)) = _
      rw [← expand_mul]
      have hpr : p ^ r * p = p ^ (r + 1) := (pow_succ p r).symm
      congr 1

theorem eq_zero_of_forall_linearPart_eq_zero (δ : Φ.Hom Φ')
    (hall : ∀ r, MvFormalGroup.linearPart (seq (p := p) δ r) = 0) : δ = 0 := by
  apply MvFormalGroup.Hom.ext
  funext i
  rw [MvFormalGroup.Hom.toPowerSeries_zero']
  ext m
  rw [map_zero]
  by_cases hm : m = 0
  · rw [hm, coeff_zero_eq_constantCoeff_apply, δ.constantCoeff_eq_zero i]
  · obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hm (Finsupp.ext hcon)
    obtain ⟨-, hExp⟩ := inv_of_forall_lt (p := p) δ (m j) fun s _ => hall s
    rw [hExp i]
    refine coeff_expand_of_not_dvd (p ^ m j) _ _ (i := j) fun hdvd => ?_
    have hlt : m j < p ^ m j := Nat.lt_pow_self hp.out.one_lt
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj) hdvd) (not_le.mpr hlt)

theorem eq_zero_of_forall_subst_eq_zero [Φ.IsComm] (δ : Φ.Hom Φ')
    (hδ : ∀ (f : MvFormalGroup.CartierModule p Φ) (i : Fin d'),
      subst f.toPowerSeries (δ.toPowerSeries i) = 0) : δ = 0 := by
  classical
  by_cases hex : ∃ r, MvFormalGroup.linearPart (seq (p := p) δ r) ≠ 0
  · exfalso

    set r := Nat.find hex with hrdef
    have hr : MvFormalGroup.linearPart (seq (p := p) δ r) ≠ 0 := Nat.find_spec hex
    have hlt : ∀ s, s < r → MvFormalGroup.linearPart (seq (p := p) δ s) = 0 := fun s hs =>
      not_not.mp (Nat.find_min hex hs)
    obtain ⟨hHom, hExp⟩ := inv_of_forall_lt (p := p) δ r hlt
    set θ := seq (p := p) δ r with hθdef
    obtain ⟨i, jj, hij⟩ : ∃ i jj, MvFormalGroup.linearPart θ i jj ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hr (Matrix.ext fun i j => by rw [hcon i j]; rfl)

    obtain ⟨f, hf⟩ := MvFormalGroup.CartierModule.tangent_surjective p Φ (Pi.single jj 1)

    have hpr : p ^ r ≠ 0 := pow_ne_zero r hp.out.ne_zero
    set c : Fin d → MvPowerSeries ℕ R :=
      fun l => map (iterateFrobenius R p r) (f.toPowerSeries l) with hcdef
    have hc0 : ∀ l, (c l).constantCoeff = 0 := fun l => by
      rw [hcdef]
      show constantCoeff (map (iterateFrobenius R p r) (f.toPowerSeries l)) = 0
      rw [constantCoeff_map, f.constantCoeff_eq_zero l, map_zero]
    have hc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
    have Z := hδ f i
    rw [hExp i, subst_expand f.hasSubst_toPowerSeries (p ^ r) hpr] at Z
    have hfam : (fun l => f.toPowerSeries l ^ p ^ r) = fun l => expand (p ^ r) hpr (c l) :=
      funext fun l => pow_eq_expand_map_iterateFrobenius (f.toPowerSeries l) r
    rw [hfam, ← MvPowerSeries.expand_subst (p ^ r) hpr hc] at Z
    have S0 : subst c (θ i) = 0 :=
      expand_injective (p ^ r) hpr (Z.trans (map_zero (expand (p ^ r) hpr)).symm)

    have hcoef := congrArg (coeff (Finsupp.single 0 1)) S0
    rw [map_zero, MvFormalGroup.coeff_single_subst hc0 (θ i) 0] at hcoef
    have hterm : ∀ l : Fin d, coeff (Finsupp.single l 1) (θ i) * coeff (Finsupp.single 0 1) (c l) =
        if l = jj then MvFormalGroup.linearPart θ i jj else 0 := by
      intro l
      have hcl : coeff (Finsupp.single 0 1) (c l) = if l = jj then 1 else 0 := by
        show coeff (Finsupp.single 0 1) (map (iterateFrobenius R p r) (f.toPowerSeries l)) = _
        rw [coeff_map, ← MvFormalGroup.CartierModule.tangent_apply, hf, Pi.single_apply]
        split_ifs
        · exact map_one _
        · exact map_zero _
      rw [hcl]
      split_ifs with hl
      · subst hl
        rw [mul_one]
        rfl
      · rw [mul_zero]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hcoef
    exact hij hcoef
  · push Not at hex
    exact eq_zero_of_forall_linearPart_eq_zero δ hex

def mapAt [Φ.IsComm] [Φ'.IsComm] (f : MvFormalGroup.CartierModule p Φ) :
    Φ.Hom Φ' →+ MvFormalGroup.CartierModule p Φ' where
  toFun χ := MvFormalGroup.CartierModule.map χ f
  map_zero' := MvFormalGroup.CartierModule.map_zero_hom f
  map_add' a b := MvFormalGroup.CartierModule.map_add_hom a b f

theorem eq_of_map_eq [Φ.IsComm] [Φ'.IsComm] (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by
  have hδ : φ - ψ = 0 := by
    refine eq_zero_of_forall_subst_eq_zero (p := p) (φ - ψ) fun f i => ?_
    have hmap : MvFormalGroup.CartierModule.map (φ - ψ) f = 0 := by
      show mapAt (p := p) f (φ - ψ) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (h f)
    have := congrArg (fun g : MvFormalGroup.CartierModule p Φ' => g.toPowerSeries i) hmap
    simpa only [MvFormalGroup.CartierModule.toPowerSeries_map,
      MvFormalGroup.CartierModule.toPowerSeries_zero] using this
  exact sub_eq_zero.mp hδ

end Descent

end P2mKcCartierFaithful

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
    (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ :=
  P2mKcCartierFaithful.eq_of_map_eq φ ψ h

end

end S_MvFormalGroup_CartierModule_eq_of_map_eq
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq (solution)
