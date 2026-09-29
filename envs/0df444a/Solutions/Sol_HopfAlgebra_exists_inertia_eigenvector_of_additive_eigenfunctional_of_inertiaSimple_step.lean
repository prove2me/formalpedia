-- Prove2me | solution 1 for HopfAlgebra.exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c41d632-39ed-5bc8-a356-902fb1a0e55c

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Lemmas
import Theorems.Thm_ValuationSubring_tameCharacter_pow_left
import Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Polynomial

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) (hs : 1 ≤ s) (hcard : Nat.card K' = p ^ s * Nat.card K)
    (hFK : ∀ f ∈ K, F f = 0) (hFK' : ∃ f ∈ K', F f ≠ 0)
    (π' : AlgebraicClosure ℚ) (hπ' : π' ^ (p ^ s - 1) = p)
    (D₀ : Finset ℕ) (hD₀ : ∀ j ∈ D₀, j < s)
    (L : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hLmul : ∀ f ∈ K', ∀ g ∈ K', L (f * g) = L f + L g) (hLK : ∀ f ∈ K, L f = 0)
    (hLK' : ∃ f ∈ K', L f ≠ 0)
    (hLeig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → L g = P.tameCharacter π' σ ^ (∑ j ∈ D₀, p ^ j) * L f) :
    ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  set θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P :=
    fun σ => P.tameCharacter π' σ with hθ
  set n₀ : ℕ := ∑ j ∈ D₀, p ^ j with hn₀
  have hq1 : 1 ≤ p ^ s - 1 := by
    have : 2 ≤ p ^ s := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : π' ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega)] at hπ'; exact hp0 hπ'.symm

  let gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    fun σ f => WithConv.toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv f))
  have gal_apply : ∀ σ f (h : H), gal σ f h = σ (f h) := fun σ f h => rfl
  have gal_one : ∀ f, gal 1 f = f := fun f => rfl
  have gal_mul : ∀ σ τ f, gal (σ * τ) f = gal σ (gal τ f) := fun σ τ f => rfl
  have hgalK' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K', gal σ f ∈ K' :=
    fun σ hσ f hf => hK' σ hσ f hf (gal σ f) (gal_apply σ f)
  have hFgal : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f, F (gal σ f) = act σ (F f) :=
    fun σ hσ f => hFequiv σ hσ f (gal σ f) (gal_apply σ f)
  have hLgal1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K', L (gal σ f) = θ σ ^ n₀ * L f :=
    fun σ hσ f hf => hLeig σ hσ f hf (gal σ f) (gal_apply σ f)

  have hθp : ∀ σ, P.tameCharacter (p : AlgebraicClosure ℚ) σ = 1 := by
    intro σ
    have hσp : σ (p : AlgebraicClosure ℚ) = p := map_natCast σ p
    have h1 : σ (p : AlgebraicClosure ℚ) / p = 1 := by rw [hσp, div_self hp0]
    have hmem : σ (p : AlgebraicClosure ℚ) / p ∈ P := by rw [h1]; exact P.one_mem
    unfold ValuationSubring.tameCharacter
    rw [dif_pos hmem]
    have : (⟨σ (p : AlgebraicClosure ℚ) / p, hmem⟩ : P) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hθpow : ∀ σ ∈ P.inertiaSubgroupIn ℚ, θ σ ^ (p ^ s - 1) = 1 := by
    intro σ hσ
    have h := ValuationSubring.tameCharacter_pow_left P π' σ (p ^ s - 1)
    rw [hπ', hθp] at h
    exact h.symm
  have hθq : ∀ σ ∈ P.inertiaSubgroupIn ℚ, θ σ ^ p ^ s = θ σ := by
    intro σ hσ
    have h := hθpow σ hσ
    calc θ σ ^ p ^ s = θ σ ^ (p ^ s - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = θ σ := by rw [pow_succ, h, one_mul]
  have hθne : ∀ σ ∈ P.inertiaSubgroupIn ℚ, θ σ ≠ 0 := by
    intro σ hσ h0
    have := hθpow σ hσ; rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this
  have hθmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ, θ (σ * τ) = θ σ * θ τ :=
    fun σ hσ τ => ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P π' hπ0 hσ τ
  have hθone : θ 1 = 1 := by
    have h := hθmul 1 (P.inertiaSubgroupIn ℚ).one_mem 1
    rw [one_mul] at h
    have h1 : θ 1 * (θ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (hθne 1 (P.inertiaSubgroupIn ℚ).one_mem)
    · exact sub_eq_zero.mp h2

  have hpk : (p : IsLocalRing.ResidueField P) = 0 := by
    have hmem : ((p : P) : AlgebraicClosure ℚ) ∈ P.nonunits := by
      have : ((p : P) : AlgebraicClosure ℚ) = p := by simp
      rw [this]; exact hP
    have hmax : (p : P) ∈ IsLocalRing.maximalIdeal P :=
      (ValuationSubring.coe_mem_nonunits_iff).mp hmem
    rw [← map_natCast (IsLocalRing.residue P) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  haveI hchar : CharP (IsLocalRing.ResidueField P) p := by
    have hdvd : ringChar (IsLocalRing.ResidueField P) ∣ p := (ringChar.spec _ p).mp hpk
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact ringChar.eq_iff.mp h1
  haveI hexp : ExpChar (IsLocalRing.ResidueField P) p := ExpChar.prime hp
  have hpN : ∀ n : N, p • n = 0 := fun n => by
    rw [← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField P), hpk, zero_smul]

  have hL1 : L 1 = 0 := by
    have h := (hLmul 1 K'.one_mem 1 K'.one_mem).symm; rw [one_mul] at h
    exact add_left_cancel (h.trans (add_zero (L 1)).symm)
  have hF1 : F 1 = 0 := by
    have h := (hFmul 1 1).symm; rw [one_mul] at h
    exact add_left_cancel (h.trans (add_zero (F 1)).symm)
  have hLpow : ∀ f ∈ K', ∀ n : ℕ, L (f ^ n) = n • L f := by
    intro f hf n
    induction n with
    | zero => rw [pow_zero, hL1, zero_smul]
    | succ n ih => rw [pow_succ, hLmul _ (pow_mem hf n) _ hf, ih, succ_nsmul]
  have hFpow : ∀ f, ∀ n : ℕ, F (f ^ n) = n • F f := by
    intro f n
    induction n with
    | zero => rw [pow_zero, hF1, zero_smul]
    | succ n ih => rw [pow_succ, hFmul, ih, succ_nsmul]
  have hLprod : ∀ (n : ℕ) (g : ℕ → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), (∀ i, g i ∈ K') →
      (∏ i ∈ Finset.range n, g i) ∈ K' ∧
        L (∏ i ∈ Finset.range n, g i) = ∑ i ∈ Finset.range n, L (g i) := by
    intro n g hg
    induction n with
    | zero =>
      exact ⟨by rw [Finset.prod_range_zero]; exact K'.one_mem, by
        rw [Finset.prod_range_zero, Finset.sum_range_zero, hL1]⟩
    | succ n ih =>
      refine ⟨by rw [Finset.prod_range_succ]; exact K'.mul_mem ih.1 (hg n), ?_⟩
      rw [Finset.prod_range_succ, Finset.sum_range_succ, hLmul _ ih.1 _ (hg n), ih.2]
  have hFprod : ∀ (n : ℕ) (g : ℕ → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      F (∏ i ∈ Finset.range n, g i) = ∑ i ∈ Finset.range n, F (g i) := by
    intro n g
    induction n with
    | zero => rw [Finset.prod_range_zero, Finset.sum_range_zero, hF1]
    | succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, hFmul, ih]

  have hInj : ∀ f ∈ K', L f = 0 → f ∈ K := by
    let K₁ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
      { carrier := {f | f ∈ K' ∧ L f = 0}
        mul_mem' := fun {a b} ha hb => ⟨K'.mul_mem ha.1 hb.1, by
          rw [hLmul a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
        one_mem' := ⟨K'.one_mem, hL1⟩ }
    have hKK₁ : K ≤ K₁ := fun f hf => ⟨hKK' hf, hLK f hf⟩
    have hK₁K' : K₁ ≤ K' := fun f hf => hf.1
    have hstab : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K₁, ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K₁ := by
      intro σ hσ f hf g hg
      exact ⟨hK' σ hσ f hf.1 g hg, by rw [hLeig σ hσ f hf.1 g hg, hf.2, mul_zero]⟩
    rcases hstep K₁ hKK₁ hK₁K' hstab with h | h
    · intro f hf hL0
      have : f ∈ K₁ := ⟨hf, hL0⟩
      rw [h] at this; exact this
    · exfalso
      obtain ⟨f, hf, hne⟩ := hLK'
      have : f ∈ K₁ := by rw [h]; exact hf
      exact hne this.2

  have hFL : ∀ f ∈ K', ∀ g ∈ K', L f = L g → F f = F g := by
    intro f hf g hg hfg
    have hgp : g ^ (p - 1) ∈ K' := pow_mem hg _
    have hLh : L (f * g ^ (p - 1)) = 0 := by
      rw [hLmul f hf _ hgp, hLpow g hg, hfg, ← succ_nsmul', Nat.sub_add_cancel hp.one_le,
        ← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField P), hpk, zero_smul]
    have hK0 : F (f * g ^ (p - 1)) = 0 := hFK _ (hInj _ (K'.mul_mem hf hgp) hLh)
    rw [hFmul, hFpow] at hK0
    have hpg : (p - 1) • F g + F g = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel hp.one_le]; exact hpN _
    have e1 : F f = -((p - 1) • F g) := eq_neg_of_add_eq_zero_left hK0
    have e2 : F g = -((p - 1) • F g) := eq_neg_of_add_eq_zero_right hpg
    rw [e1]; exact e2.symm

  obtain ⟨σ₀, hσ₀, hgen⟩ : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∃ m : ℕ, θ σ = θ σ₀ ^ m := by
    let Γ : Subgroup (IsLocalRing.ResidueField P)ˣ :=
      { carrier := {u | ∃ σ ∈ P.inertiaSubgroupIn ℚ, (u : IsLocalRing.ResidueField P) = θ σ}
        mul_mem' := by
          rintro a b ⟨σ, hσ, ha⟩ ⟨τ, hτ, hb⟩
          exact ⟨σ * τ, (P.inertiaSubgroupIn ℚ).mul_mem hσ hτ, by
            rw [Units.val_mul, ha, hb, hθmul σ hσ τ]⟩
        one_mem' := ⟨1, (P.inertiaSubgroupIn ℚ).one_mem, by rw [Units.val_one, hθone]⟩
        inv_mem' := by
          rintro a ⟨σ, hσ, ha⟩
          refine ⟨σ⁻¹, (P.inertiaSubgroupIn ℚ).inv_mem hσ, ?_⟩
          have h := hθmul σ hσ σ⁻¹
          rw [mul_inv_cancel, hθone] at h
          rw [Units.val_inv_eq_inv_val, ha]
          exact inv_eq_of_mul_eq_one_right h.symm }
    have hfin : Finite Γ := by
      let T := (Polynomial.nthRoots (p ^ s - 1) (1 : IsLocalRing.ResidueField P)).toFinset
      refine Finite.of_injective (fun u : Γ =>
        (⟨((u : (IsLocalRing.ResidueField P)ˣ) : IsLocalRing.ResidueField P), ?_⟩ : T)) ?_
      · obtain ⟨σ, hσ, hu⟩ := u.2
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega), hu]
        exact hθpow σ hσ
      · intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (Units.ext this)
    have hcyc : IsCyclic Γ :=
      isCyclic_of_subgroup_isDomain ((Units.coeHom _).comp Γ.subtype) (by
        intro a b hab; exact Subtype.ext (Units.ext hab))
    obtain ⟨g, hg⟩ := hcyc.exists_monoid_generator
    obtain ⟨σ₀, hσ₀, hg0⟩ := g.2
    refine ⟨σ₀, hσ₀, fun σ hσ => ?_⟩
    have hu : (Units.mk0 (θ σ) (hθne σ hσ)) ∈ Γ := ⟨σ, hσ, rfl⟩
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (hg ⟨_, hu⟩)
    refine ⟨m, ?_⟩
    have h2 := congrArg (fun x : Γ => (((x : (IsLocalRing.ResidueField P)ˣ)) : IsLocalRing.ResidueField P)) hm
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0] at h2
    rw [← h2, hg0]
  set γ : IsLocalRing.ResidueField P := θ σ₀ ^ n₀ with hγ
  have hγq : γ ^ p ^ s = γ := by
    rw [hγ, ← pow_mul, Nat.mul_comm n₀ (p ^ s), pow_mul, hθq σ₀ hσ₀]

  set V : Submodule (IsLocalRing.ResidueField P) N :=
    Submodule.span (IsLocalRing.ResidueField P) (F '' (K' : Set (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))) with hV
  have hAV : ∀ v ∈ V, act σ₀ v ∈ V := by
    have hle : V.map (act σ₀) ≤ V := by
      rw [hV, Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨gal σ₀ f, hgalK' σ₀ hσ₀ f hf, hFgal σ₀ hσ₀ f⟩
    intro v hv
    exact hle (Submodule.mem_map_of_mem hv)
  have hAF : ∀ (m : ℕ) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ((act σ₀) ^ m) (F f) = F (gal (σ₀ ^ m) f) := by
    intro m
    induction m with
    | zero => intro f; rw [pow_zero, pow_zero, gal_one, Module.End.one_apply]
    | succ m ih =>
      intro f
      rw [pow_succ, pow_succ, Module.End.mul_apply, gal_mul, ← ih, hFgal σ₀ hσ₀]
  have hLgal : ∀ (m : ℕ), ∀ f ∈ K',
      gal (σ₀ ^ m) f ∈ K' ∧ L (gal (σ₀ ^ m) f) = θ σ₀ ^ (n₀ * m) * L f := by
    intro m
    induction m with
    | zero =>
      intro f hf
      exact ⟨by rw [pow_zero, gal_one]; exact hf, by
        rw [pow_zero, gal_one, mul_zero, pow_zero, one_mul]⟩
    | succ m ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      refine ⟨by rw [pow_succ', gal_mul]; exact hgalK' σ₀ hσ₀ _ h1, ?_⟩
      rw [pow_succ', gal_mul, hLgal1 σ₀ hσ₀ _ h1, h2, ← mul_assoc, ← pow_add,
        show n₀ + n₀ * m = n₀ * (m + 1) by ring]

  have hact : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : ℕ, θ σ = θ σ₀ ^ m →
      ∀ v ∈ V, act σ v = ((act σ₀) ^ m) v := by
    intro σ hσ m hm
    have key : Set.EqOn (act σ) ((act σ₀ ^ m : Module.End (IsLocalRing.ResidueField P) N))
        (F '' (K' : Set (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))) := by
      rintro _ ⟨f, hf, rfl⟩
      show act σ (F f) = ((act σ₀) ^ m) (F f)
      rw [← hFgal σ hσ f, hAF m f]
      apply hFL _ (hgalK' σ hσ f hf) _ (hLgal m f hf).1
      rw [hLgal1 σ hσ f hf, (hLgal m f hf).2, hm, ← pow_mul, Nat.mul_comm m n₀]
    intro v hv
    exact LinearMap.eqOn_span key hv

  let gQ : ℕ → (IsLocalRing.ResidueField P)[X] := fun j => X - C (γ ^ p ^ j)
  set Q : (IsLocalRing.ResidueField P)[X] := ∏ j ∈ Finset.range s, gQ j with hQ
  have hQfrob : Q.map (frobenius (IsLocalRing.ResidueField P) p) = Q := by
    have hg : ∀ j, (gQ j).map (frobenius (IsLocalRing.ResidueField P) p) = gQ (j + 1) := by
      intro j
      show (X - C (γ ^ p ^ j)).map _ = X - C (γ ^ p ^ (j + 1))
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, frobenius_def, ← pow_mul,
        ← pow_succ]
    have hgs : gQ s = gQ 0 := by
      show X - C (γ ^ p ^ s) = X - C (γ ^ p ^ 0)
      rw [hγq, pow_zero, pow_one]
    have h1 : (∏ i ∈ Finset.range s, gQ (i + 1)) * gQ 0 = (∏ i ∈ Finset.range s, gQ i) * gQ 0 := by
      rw [← Finset.prod_range_succ', Finset.prod_range_succ, hgs]
    have hne0 : gQ 0 ≠ 0 := Polynomial.X_sub_C_ne_zero _
    have h2 := mul_right_cancel₀ hne0 h1
    calc Q.map (frobenius _ p) = ∏ i ∈ Finset.range s, (gQ i).map (frobenius _ p) := by
          rw [hQ, Polynomial.map_prod]
      _ = ∏ i ∈ Finset.range s, gQ (i + 1) := Finset.prod_congr rfl (fun i _ => hg i)
      _ = Q := by rw [h2]
  have KEY : ∀ c : IsLocalRing.ResidueField P, c ^ p = c → ∃ n : ℕ, c = n := by
    intro c hc
    let ψ := ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P)
    have hR0 : (X ^ p - X : (IsLocalRing.ResidueField P)[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero _ hp.one_lt
    have hdeg : (X ^ p - X : (IsLocalRing.ResidueField P)[X]).natDegree = p :=
      FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt
    have hroot : ∀ x, x ∈ (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots.toFinset ↔
        x ^ p = x := by
      intro x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hR0, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    let S : Finset (IsLocalRing.ResidueField P) := Finset.univ.image ψ
    have hSsub : S ⊆ (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots.toFinset := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hroot, ← map_pow, ZMod.pow_card]
    have hScard : S.card = p := by
      rw [Finset.card_image_of_injective _ ψ.injective, Finset.card_univ, ZMod.card]
    have hle : (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots.toFinset.card ≤ p := by
      calc (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots.toFinset.card
          ≤ Multiset.card (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots :=
            Multiset.toFinset_card_le _
        _ ≤ (X ^ p - X : (IsLocalRing.ResidueField P)[X]).natDegree := Polynomial.card_roots' _
        _ = p := hdeg
    have hSeq : S = (X ^ p - X : (IsLocalRing.ResidueField P)[X]).roots.toFinset :=
      Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hle)
    have hcS : c ∈ S := by rw [hSeq, hroot]; exact hc
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hcS
    exact ⟨a.val, by rw [ZMod.natCast_val, ZMod.castHom_apply]⟩
  have hQcoeff : ∀ i, ∃ n : ℕ, Q.coeff i = n := by
    intro i
    apply KEY
    have h := congrArg (fun q : (IsLocalRing.ResidueField P)[X] => q.coeff i) hQfrob
    simp only [Polynomial.coeff_map, frobenius_def] at h
    exact h
  have hev : Q.eval γ = 0 := by
    rw [hQ, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 0 < s))
    show eval γ (X - C (γ ^ p ^ 0)) = 0
    rw [pow_zero, pow_one, eval_sub, eval_X, eval_C, sub_self]
  have hQA : ∀ f ∈ K', Polynomial.aeval (act σ₀) Q (F f) = 0 := by
    intro f hf
    choose nQ hnQ using hQcoeff
    have hg : ∀ i, gal (σ₀ ^ i) f ^ nQ i ∈ K' := fun i => pow_mem (hLgal i f hf).1 _
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hAF, hnQ, Nat.cast_smul_eq_nsmul]
    rw [show ∑ i ∈ Finset.range (Q.natDegree + 1), nQ i • F (gal (σ₀ ^ i) f)
        = F (∏ i ∈ Finset.range (Q.natDegree + 1), gal (σ₀ ^ i) f ^ nQ i) by
      rw [hFprod]; simp only [hFpow]]
    apply hFK
    apply hInj _ (hLprod _ _ hg).1
    rw [(hLprod _ _ hg).2]
    calc ∑ i ∈ Finset.range (Q.natDegree + 1), L (gal (σ₀ ^ i) f ^ nQ i)
        = ∑ i ∈ Finset.range (Q.natDegree + 1), (Q.coeff i * γ ^ i) * L f := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hLpow _ (hLgal i f hf).1, (hLgal i f hf).2,
            ← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField P), ← hnQ, smul_eq_mul, hγ,
            ← pow_mul, mul_assoc]
      _ = Q.eval γ * L f := by rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      _ = 0 := by rw [hev, zero_mul]

  obtain ⟨f₀, hf₀K', hFf₀⟩ := hFK'
  let a : ℕ → IsLocalRing.ResidueField P := fun j => γ ^ p ^ j
  let v : ℕ → N := fun t => Nat.rec (F f₀) (fun j vj => act σ₀ vj - a j • vj) t
  have hv0 : v 0 = F f₀ := rfl
  have hvs : ∀ t, v (t + 1) = act σ₀ (v t) - a t • v t := fun t => rfl
  have hvV : ∀ t, v t ∈ V := by
    intro t
    induction t with
    | zero => rw [hv0]; exact Submodule.subset_span ⟨f₀, hf₀K', rfl⟩
    | succ t ih => rw [hvs]; exact V.sub_mem (hAV _ ih) (V.smul_mem _ ih)
  have hvQ : ∀ t, v t = Polynomial.aeval (act σ₀) (∏ j ∈ Finset.range t, gQ j) (F f₀) := by
    intro t
    induction t with
    | zero => rw [Finset.prod_range_zero, map_one, Module.End.one_apply, hv0]
    | succ t ih =>
      rw [hvs, Finset.prod_range_succ, mul_comm (∏ j ∈ Finset.range t, gQ j) (gQ t), map_mul,
        Module.End.mul_apply, ← ih]
      show act σ₀ (v t) - a t • v t = Polynomial.aeval (act σ₀) (X - C (γ ^ p ^ t)) (v t)
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
  have hvs0 : v s = 0 := by rw [hvQ]; exact hQA f₀ hf₀K'
  have hex : ∃ t, v (t + 1) = 0 := ⟨s - 1, by rw [Nat.sub_add_cancel hs]; exact hvs0⟩
  obtain ⟨t, ht1, htmin⟩ : ∃ t, v (t + 1) = 0 ∧ ∀ u, u < t → v (u + 1) ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩
  have hts : t < s := by
    by_contra hge
    exact htmin (s - 1) (by omega) (by rw [Nat.sub_add_cancel hs]; exact hvs0)
  have hvt : v t ≠ 0 := by
    intro h0
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · rw [ht0, hv0] at h0; exact hFf₀ h0
    · exact htmin (t - 1) (by omega) (by rw [Nat.sub_add_cancel htpos]; exact h0)
  have hAw : act σ₀ (v t) = a t • v t := sub_eq_zero.mp (by rw [← hvs]; exact ht1)
  have h2 : ∀ m : ℕ, ((act σ₀) ^ m) (v t) = (a t) ^ m • v t := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hAw, smul_smul, ← pow_succ]

  have hrot : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      θ σ ^ (n₀ * p ^ t) = θ σ ^ (∑ j ∈ D₀.image (fun d => (d + t) % s), p ^ j) := by
    intro σ hσ
    have hinj : ∀ d₁ ∈ D₀, ∀ d₂ ∈ D₀, (d₁ + t) % s = (d₂ + t) % s → d₁ = d₂ := by
      intro d₁ hd₁ d₂ hd₂ he
      have h1 := hD₀ d₁ hd₁
      have h2 := hD₀ d₂ hd₂
      have h3 : d₁ % s = d₂ % s := Nat.ModEq.add_right_cancel' t he
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h3
    rw [Finset.sum_image hinj, hn₀, Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro d _
    have key : ∀ x : IsLocalRing.ResidueField P, x ^ p ^ s = x → ∀ b : ℕ, x ^ (p ^ s) ^ b = x := by
      intro x hx b
      induction b with
      | zero => rw [pow_zero, pow_one]
      | succ b ih => rw [pow_succ, pow_mul, ih, hx]
    have hx : (θ σ ^ p ^ ((d + t) % s)) ^ p ^ s = θ σ ^ p ^ ((d + t) % s) := by
      rw [← pow_mul, Nat.mul_comm (p ^ ((d + t) % s)) (p ^ s), pow_mul, hθq σ hσ]
    calc θ σ ^ (p ^ d * p ^ t) = θ σ ^ (p ^ ((d + t) % s) * (p ^ s) ^ ((d + t) / s)) := by
          rw [← pow_add, ← pow_mul, ← pow_add p, Nat.mod_add_div]
      _ = θ σ ^ p ^ ((d + t) % s) := by rw [pow_mul, key _ hx]

  refine ⟨D₀.image (fun d => (d + t) % s), ?_, v t, hvt, ?_⟩
  · intro j hj
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hj
    exact Nat.mod_lt _ (by omega)
  · intro σ hσ
    obtain ⟨m, hm⟩ := hgen σ hσ
    rw [hact σ hσ m hm _ (hvV t), h2 m, ← hrot σ hσ]
    show (γ ^ p ^ t) ^ m • v t = θ σ ^ (n₀ * p ^ t) • v t
    rw [hγ, ← pow_mul, ← pow_mul, hm, ← pow_mul, show m * (n₀ * p ^ t) = n₀ * (p ^ t * m) by ring]

end S_HopfAlgebra_exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step
end P2MW
export P2MW.S_HopfAlgebra_exists_inertia_eigenvector_of_additive_eigenfunctional_of_inertiaSimple_step (solution)
