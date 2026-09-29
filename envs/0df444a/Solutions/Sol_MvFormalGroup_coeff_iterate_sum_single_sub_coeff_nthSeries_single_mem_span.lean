-- Prove2me | solution 1 for MvFormalGroup.coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/de354d00-0c34-584b-8455-6655a7f4bdcb

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span

set_option autoImplicit false

open MvPowerSeries
open scoped TensorProduct

universe u

noncomputable section

namespace HNAOrbit

section Orbit

private def Tup (ι : Type*) (p : ℕ) : Type _ := ZMod p → ι

namespace Tup

variable {ι : Type*} {p : ℕ}

private scoped instance instFintype [Fintype ι] [NeZero p] : Fintype (Tup ι p) :=
  inferInstanceAs (Fintype (ZMod p → ι))

private scoped instance instMulAction : MulAction (Multiplicative (ZMod p)) (Tup ι p) where
  smul r I := fun j => I (j + Multiplicative.toAdd r)
  one_smul I := funext fun j => by
    change I (j + Multiplicative.toAdd (1 : Multiplicative (ZMod p))) = I j
    rw [toAdd_one, add_zero]
  mul_smul r s I := funext fun j => by
    change I (j + Multiplicative.toAdd (r * s)) =
      I (j + Multiplicative.toAdd r + Multiplicative.toAdd s)
    rw [toAdd_mul, add_assoc]

private theorem smul_apply (r : Multiplicative (ZMod p)) (I : Tup ι p) (j : ZMod p) :
    (r • I) j = I (j + Multiplicative.toAdd r) := rfl

private def const (i : ι) : Tup ι p := fun _ => i

@[scoped simp] private theorem const_apply (i : ι) (j : ZMod p) : (const i : Tup ι p) j = i := rfl

private theorem smul_const (r : Multiplicative (ZMod p)) (i : ι) :
    (r • (const i : Tup ι p)) = const i := rfl

private theorem eq_const_of_mem_fixedPoints {I : Tup ι p}
    (hI : I ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (Tup ι p)) :
    I = const (I 0) := by
  funext j
  have h := congrFun (MulAction.mem_fixedPoints.1 hI (Multiplicative.ofAdd j)) 0
  rw [smul_apply, toAdd_ofAdd, zero_add] at h
  exact h

private theorem const_mem_fixedPoints (i : ι) :
    (const i : Tup ι p) ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (Tup ι p) :=
  MulAction.mem_fixedPoints.2 fun _ => rfl

private theorem eq_const_of_mem_orbit_const {i : ι} {I : Tup ι p}
    (hI : I ∈ MulAction.orbit (Multiplicative (ZMod p)) (const i : Tup ι p)) :
    I = const i := by
  obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.1 hI
  rfl

private theorem sum_eq_sum_const [Fintype ι] [hp : Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (hM : ∀ m : M, p • m = 0) (g : Tup ι p → M)
    (hg : ∀ (r : Multiplicative (ZMod p)) (I : Tup ι p), g (r • I) = g I) :
    ∑ I : Tup ι p, g I = ∑ i : ι, g (const i) := by
  classical
  set G := Multiplicative (ZMod p) with hG
  have hcardG : Fintype.card G = p := by simp [G]
  letI : Fintype (MulAction.orbitRel.Quotient G (Tup ι p)) :=
    @Quotient.fintype _ _ (MulAction.orbitRel G (Tup ι p)) (fun _ _ => Classical.propDecidable _)
  let e := MulAction.selfEquivSigmaOrbits' G (Tup ι p)

  have hout : ∀ (ω : MulAction.orbitRel.Quotient G (Tup ι p)) (y : Tup ι p), y ∈ ω.orbit →
      g y = g ω.out := by
    intro ω y hy
    have hy' : y ∈ MulAction.orbit G ω.out := by
      rw [MulAction.orbitRel.Quotient.mem_orbit] at hy
      have h2 : Quotient.mk'' ω.out = ω := Quotient.out_eq' ω
      have := Quotient.exact' (hy.trans h2.symm)
      exact (MulAction.orbitRel_apply).1 this
    obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.1 hy'
    exact hg r _

  have horb : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      ω.orbit = MulAction.orbit G ω.out := fun ω =>
    MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq'

  have hsize : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      Fintype.card (MulAction.orbit G ω.out) = 1 ∨ Fintype.card (MulAction.orbit G ω.out) = p := by
    intro ω
    apply hp.out.eq_one_or_self_of_dvd
    refine ⟨Fintype.card (MulAction.stabilizer G ω.out), ?_⟩
    rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group, hcardG]

  have step1 : ∑ I : Tup ι p, g I =
      ∑ ω : MulAction.orbitRel.Quotient G (Tup ι p),
        Fintype.card (MulAction.orbit G ω.out) • g ω.out := by
    rw [← Equiv.sum_comp e.symm g, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hval : ∀ y : ω.orbit, g (e.symm ⟨ω, y⟩) = g ω.out := fun y => hout ω y.1 y.2
    rw [Fintype.sum_congr _ _ hval, Finset.sum_const, Finset.card_univ]
    congr 1
    exact Fintype.card_congr (Equiv.setCongr (horb ω))

  have step2 : ∀ ω : MulAction.orbitRel.Quotient G (Tup ι p),
      Fintype.card (MulAction.orbit G ω.out) • g ω.out =
        if Fintype.card (MulAction.orbit G ω.out) = 1 then g (const (ω.out 0)) else 0 := by
    intro ω
    rcases hsize ω with h1 | hP
    · rw [if_pos h1, h1, one_smul]
      have hfix := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).2 h1
      rw [← eq_const_of_mem_fixedPoints hfix]
    · rw [hP, hM, if_neg]
      exact hp.out.one_lt.ne'
  rw [step1, Fintype.sum_congr _ _ step2, Finset.sum_ite, Finset.sum_const_zero, add_zero]

  have hout_const : ∀ i : ι,
      (Quotient.mk'' (const i : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)).out =
        const i := by
    intro i
    apply eq_const_of_mem_orbit_const
    apply (MulAction.orbitRel_apply).1
    exact Quotient.exact' (Quotient.out_eq' _)
  symm
  refine Finset.sum_nbij' (fun i => (Quotient.mk'' (const i : Tup ι p)))
    (fun ω => ω.out 0) ?_ ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hout_const]
    exact ⟨Finset.mem_univ _,
      (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).1 (const_mem_fixedPoints i)⟩
  · intro ω _
    exact Finset.mem_univ _
  · intro i _
    change (Quotient.mk'' (const i : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)).out 0 = i
    rw [hout_const]
    rfl
  · intro ω hω
    rw [Finset.mem_filter] at hω
    have hfix := (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).2 hω.2
    change (Quotient.mk'' (const (ω.out 0) : Tup ι p) : MulAction.orbitRel.Quotient G (Tup ι p)) = ω
    rw [← eq_const_of_mem_fixedPoints hfix]
    exact Quotient.out_eq' ω
  · intro i _
    rw [hout_const]
    rfl

end Tup
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup"

end Orbit
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup"

section FinTransport

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

private noncomputable def finZ : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv

private noncomputable def ρ : Tup ι p ≃ (Fin p → ι) := Equiv.arrowCongr (finZ p).symm (Equiv.refl ι)

private theorem ρ_apply (T : Tup ι p) (j : Fin p) : ρ p T j = T (finZ p j) := rfl

private noncomputable def rot (r : Multiplicative (ZMod p)) : Equiv.Perm (Fin p) :=
  ((finZ p).trans (Equiv.addRight (Multiplicative.toAdd r))).trans (finZ p).symm

private theorem ρ_smul (r : Multiplicative (ZMod p)) (T : Tup ι p) : ρ p (r • T) = ρ p T ∘ rot p r := by
  funext j
  change T (finZ p j + Multiplicative.toAdd r) = T (finZ p ((finZ p).symm (finZ p j + Multiplicative.toAdd r)))
  rw [Equiv.apply_symm_apply]

private theorem ρ_const (i : ι) : ρ p (Tup.const i : Tup ι p) = fun _ => i := rfl

variable [Fintype ι] in

private theorem sum_eq_sum_const_fin {M : Type*} [AddCommMonoid M] (hM : ∀ m : M, p • m = 0)
    (g : (Fin p → ι) → M) (hg : ∀ (σ : Equiv.Perm (Fin p)) (I : Fin p → ι), g (I ∘ σ) = g I) :
    ∑ I : Fin p → ι, g I = ∑ i : ι, g (fun _ => i) := by
  rw [← Equiv.sum_comp (ρ p)]
  rw [Tup.sum_eq_sum_const hM (fun T => g (ρ p T)) (fun r T => by
    change g (ρ p (r • T)) = g (ρ p T)
    rw [ρ_smul, hg])]
  rfl

end FinTransport
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup"

end HNAOrbit
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

namespace HNABody

section Rename

variable {𝓞 : Type u} [CommRing 𝓞] {σ σ' τ : Type*} (f : σ → τ) [Filter.TendstoCofinite f]

private theorem rename_subst {a : σ' → MvPowerSeries σ 𝓞} (ha : HasSubst a) (φ : MvPowerSeries σ' 𝓞) :
    rename f (subst a φ) = subst (fun s => rename f (a s)) φ := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp f)]
  congr 1
  funext s
  rw [rename_eq_subst]

end Rename
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

section Iter

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞)
  (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
  (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
  (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
    subst (Sum.elim
      (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
        MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
      (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
      (F.toPowerSeries k))

private def emb (n : ℕ) : Fin n × Fin d → Fin (n + 1) × Fin d := fun sj => (Fin.castSucc sj.1, sj.2)

private theorem emb_injective (n : ℕ) : Function.Injective (emb (d := d) n) := by
  rintro ⟨s, j⟩ ⟨s', j'⟩ h
  simp only [emb, Prod.mk.injEq, Fin.castSucc_inj] at h
  rw [h.1, h.2]

private scoped instance (n : ℕ) : Filter.TendstoCofinite (emb (d := d) n) := Filter.tendstoCofinite_of_injective (emb_injective n)

private theorem subst_X_emb_eq_rename (n : ℕ) (φ : MvPowerSeries (Fin n × Fin d) 𝓞) :
    subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) φ =
      rename (emb n) φ := by
  rw [rename_eq_subst]; rfl

include hG1 hGsucc in

private theorem constantCoeff_G : ∀ (m : ℕ) (k : Fin d), constantCoeff (G (m + 1) k) = 0
  | 0, k => by rw [hG1, constantCoeff_X]
  | m + 1, k => by
    rw [hGsucc (m + 1) k]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (F.constantCoeff_eq_zero k) <;>
    · rintro (j | j)
      · rw [Sum.elim_inl, subst_X_emb_eq_rename, constantCoeff_rename]
        exact constantCoeff_G m j
      · rw [Sum.elim_inr, constantCoeff_X]

include hG1 hGsucc in
private theorem hasSubst_fam (m : ℕ) : HasSubst (Sum.elim
      (fun j => subst (fun sj : Fin (m + 1) × Fin d => (X (Fin.castSucc sj.1, sj.2) :
        MvPowerSeries (Fin (m + 1 + 1) × Fin d) 𝓞)) (G (m + 1) j))
      (fun j => (X (Fin.last (m + 1), j) : MvPowerSeries (Fin (m + 1 + 1) × Fin d) 𝓞))) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · rw [Sum.elim_inl, subst_X_emb_eq_rename, constantCoeff_rename]
    exact constantCoeff_G F G hG1 hGsucc m j
  · rw [Sum.elim_inr, constantCoeff_X]

private scoped instance (n : ℕ) : Filter.TendstoCofinite (Prod.snd : Fin n × Fin d → Fin d) := Filter.tendstoCofinite_of_finite _

include hG1 hGsucc in

private theorem rename_snd_G : ∀ (m : ℕ) (k : Fin d), rename Prod.snd (G (m + 1) k) = F.nthSeries (m + 1) k
  | 0, k => by
    rw [hG1, rename_X, MvFormalGroup.nthSeries_succ]
    change (X k : MvPowerSeries (Fin d) 𝓞) = subst (Sum.elim (F.nthSeries 0) fun j => X j) (F.toPowerSeries k)
    rw [MvFormalGroup.nthSeries_zero, MvFormalGroup.subst_elim_zero_left F (fun j => constantCoeff_X j) k]
  | m + 1, k => by
    rw [hGsucc (m + 1) k, rename_subst Prod.snd (hasSubst_fam F G hG1 hGsucc m), MvFormalGroup.nthSeries_succ]
    congr 1
    funext s
    rcases s with j | j
    · rw [Sum.elim_inl, Sum.elim_inl, subst_X_emb_eq_rename, rename_rename, ← rename_snd_G m j]
      rfl
    · rw [Sum.elim_inr, Sum.elim_inr, rename_X]

end Iter
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

section Perm

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
  (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
  (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
  (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
    subst (Sum.elim
      (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
        MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
      (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
      (F.toPowerSeries k))

private abbrev pm {n : ℕ} (τ : Equiv.Perm (Fin n)) : Fin n × Fin d → Fin n × Fin d := Prod.map τ id

private scoped instance {n : ℕ} (τ : Equiv.Perm (Fin n)) : Filter.TendstoCofinite (pm (d := d) τ) :=
  Filter.tendstoCofinite_of_finite _

omit [F.IsComm] in
private theorem rename_congr {σ τ : Type*} {f g : σ → τ} [Filter.TendstoCofinite f] [Filter.TendstoCofinite g]
    (h : f = g) (φ : MvPowerSeries σ 𝓞) : rename f φ = rename g φ := by
  subst h; rfl

omit [F.IsComm] in
private theorem rename_pm_one {n : ℕ} (φ : MvPowerSeries (Fin n × Fin d) 𝓞) :
    rename (pm (1 : Equiv.Perm (Fin n))) φ = φ := by
  rw [rename_eq_subst]
  have : (X ∘ pm (d := d) (1 : Equiv.Perm (Fin n)) : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) 𝓞) = X := by
    funext x; rfl
  rw [this]
  exact congrFun subst_self φ

omit [F.IsComm] in
private theorem rename_pm_mul {n : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin n)) (φ : MvPowerSeries (Fin n × Fin d) 𝓞) :
    rename (pm (τ₁ * τ₂)) φ = rename (pm τ₁) (rename (pm τ₂) φ) := by
  rw [rename_rename]
  exact rename_congr (funext fun x => rfl) φ

omit [F.IsComm] in
include hG1 hGsucc in
set_option linter.unusedSimpArgs false in

private theorem G_succ_succ (m : ℕ) (k : Fin d) :
    G (m + 1 + 1 + 1) k =
      subst (Sum.elim
        (fun j => subst (Sum.elim
          (fun j' => rename (emb (m + 1 + 1)) (rename (emb (m + 1)) (G (m + 1) j')))
          (fun j' => (X (Fin.castSucc (Fin.last (m + 1)), j') : MvPowerSeries (Fin (m + 1 + 1 + 1) × Fin d) 𝓞)))
          (F.toPowerSeries j))
        (fun j => (X (Fin.last (m + 1 + 1), j) : MvPowerSeries (Fin (m + 1 + 1 + 1) × Fin d) 𝓞)))
      (F.toPowerSeries k) := by
  rw [hGsucc (m + 1 + 1) k]
  congr 1
  funext s
  rcases s with j | j
  · (try simp only [Sum.elim_inl, Sum.elim_inr])
    rw [subst_X_emb_eq_rename, hGsucc (m + 1) j, rename_subst (emb (m + 1 + 1)) (hasSubst_fam F G hG1 hGsucc m)]
    congr 1
    funext s'
    rcases s' with j' | j'
    · (try simp only [Sum.elim_inl, Sum.elim_inr]); rw [subst_X_emb_eq_rename]
    · (try simp only [Sum.elim_inl, Sum.elim_inr]); rw [rename_X]; rfl
  · rfl

include hG1 hGsucc in
set_option linter.unusedSimpArgs false in

private theorem rename_pm_G : ∀ (m : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (k : Fin d),
    rename (pm τ) (G (m + 1) k) = G (m + 1) k
  | 0, τ, k => by
    have hτ : τ = 1 := Equiv.ext fun x => by
      have h1 : ∀ y : Fin (0 + 1), y = 0 := fun y => Fin.ext (by have := y.2; omega)
      rw [h1 (τ x), h1 ((1 : Equiv.Perm (Fin (0 + 1))) x)]
    rw [hτ, rename_pm_one]
  | m + 1, τ, k => by

    suffices h : ∀ τ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ),
        ∀ k, rename (pm τ) (G (m + 1 + 1) k) = G (m + 1 + 1) k by
      exact h τ (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top τ) k
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | one => intro k; exact rename_pm_one _
    | mul τ₁ τ₂ _ _ h₁ h₂ => intro k; rw [rename_pm_mul, h₂, h₁]
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      intro k

      have hc0 : ∀ (n : ℕ) (j : Fin d), constantCoeff (G (n + 1) j) = 0 := constantCoeff_G F G hG1 hGsucc
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      ·
        have hcomm : pm (d := d) (Equiv.swap i'.castSucc.castSucc i'.castSucc.succ) ∘ emb (m + 1) =
            emb (m + 1) ∘ pm (Equiv.swap i'.castSucc i'.succ) := by
          funext ⟨s, j⟩
          simp only [Function.comp_apply, pm, emb, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
          rw [show i'.castSucc.succ = i'.succ.castSucc from rfl]
          exact (Fin.castSucc_injective _).map_swap _ _ _ ▸ rfl
        rw [hGsucc (m + 1) k, rename_subst _ (hasSubst_fam F G hG1 hGsucc m)]
        congr 1
        funext s
        rcases s with j | j
        · (try simp only [Sum.elim_inl, Sum.elim_inr])
          rw [subst_X_emb_eq_rename, rename_rename, rename_congr hcomm, ← rename_rename, rename_pm_G m _ j]
        · (try simp only [Sum.elim_inl, Sum.elim_inr])
          rw [rename_X]
          congr 1
          simp only [pm, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
          rw [show i'.castSucc.succ = i'.succ.castSucc from rfl]
          exact Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne' (Fin.castSucc_lt_last _).ne'
      ·
        cases m with
        | zero =>

          have hG2 : G (0 + 1 + 1) k = subst (Sum.elim
              (fun j => (X ((0 : Fin 2), j) : MvPowerSeries (Fin (0 + 1 + 1) × Fin d) 𝓞))
              (fun j => (X ((1 : Fin 2), j) : MvPowerSeries (Fin (0 + 1 + 1) × Fin d) 𝓞))) (F.toPowerSeries k) := by
            rw [hGsucc 1 k]
            congr 1
            funext s
            rcases s with j | j
            · (try simp only [Sum.elim_inl, Sum.elim_inr]); rw [hG1, subst_X_emb_eq_rename, rename_X]; rfl
            · rfl
          rw [hG2, rename_subst _ (MvFormalGroup.hasSubst_elim (fun j => constantCoeff_X _) (fun j => constantCoeff_X _)),
            MvFormalGroup.subst_elim_comm F (fun j => constantCoeff_X _) (fun j => constantCoeff_X _) k]
          congr 1
          funext s
          rcases s with j | j
          · (try simp only [Sum.elim_inl, Sum.elim_inr]); rw [rename_X]; rfl
          · (try simp only [Sum.elim_inl, Sum.elim_inr]); rw [rename_X]; rfl
        | succ m =>
          set A : Fin d → MvPowerSeries (Fin (m + 1 + 1 + 1) × Fin d) 𝓞 :=
            fun j' => rename (emb (m + 1 + 1)) (rename (emb (m + 1)) (G (m + 1) j')) with hA
          set B : Fin d → MvPowerSeries (Fin (m + 1 + 1 + 1) × Fin d) 𝓞 :=
            fun j' => X (Fin.castSucc (Fin.last (m + 1)), j') with hB
          set C : Fin d → MvPowerSeries (Fin (m + 1 + 1 + 1) × Fin d) 𝓞 :=
            fun j' => X (Fin.last (m + 1 + 1), j') with hC
          have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by
            rw [hA]; dsimp only; rw [constantCoeff_rename, constantCoeff_rename]; exact hc0 m j
          have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => constantCoeff_X _
          have hC0 : ∀ j, constantCoeff (C j) = 0 := fun j => constantCoeff_X _
          set σ := Equiv.swap (Fin.last (m + 1)).castSucc (Fin.last (m + 1)).succ with hσ
          have hσA : ∀ j, rename (pm σ) (A j) = A j := by
            intro j
            rw [hA]; dsimp only
            rw [rename_rename, rename_rename, rename_rename]
            refine rename_congr (funext fun ⟨s, j'⟩ => ?_) _
            simp only [Function.comp_apply, pm, emb, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
            exact Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_castSucc_iff.2 (Fin.castSucc_lt_last s)).ne
              (by rw [Fin.succ_last]; exact (Fin.castSucc_lt_last _).ne)
          have hσB : ∀ j, rename (pm σ) (B j) = C j := by
            intro j
            rw [hB, hC]; dsimp only
            rw [rename_X]
            congr 1
            simp only [pm, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
            rw [Equiv.swap_apply_left, Fin.succ_last]
          have hσC : ∀ j, rename (pm σ) (C j) = B j := by
            intro j
            rw [hB, hC]; dsimp only
            rw [rename_X]
            congr 1
            simp only [pm, Prod.map_apply, id_eq, Prod.mk.injEq, and_true]
            rw [← Fin.succ_last, Equiv.swap_apply_right]
          have hAB : HasSubst (Sum.elim A B) := MvFormalGroup.hasSubst_elim hA0 hB0
          have hFAB0 : ∀ j, constantCoeff (subst (Sum.elim A B) (F.toPowerSeries j)) = 0 := fun j =>
            constantCoeff_subst_eq_zero hAB (by rintro (l | l) <;> simp only [Sum.elim_inl, Sum.elim_inr, hA0, hB0])
              (F.constantCoeff_eq_zero j)
          have hT : HasSubst (Sum.elim (fun j => subst (Sum.elim A B) (F.toPowerSeries j)) C) :=
            MvFormalGroup.hasSubst_elim hFAB0 hC0
          have hG3 : G (m + 1 + 1 + 1) k = subst (Sum.elim (fun j => subst (Sum.elim A B) (F.toPowerSeries j)) C)
              (F.toPowerSeries k) := G_succ_succ F G hG1 hGsucc m k

          have hL : (fun t => rename (pm σ) (Sum.elim (fun j => subst (Sum.elim A B) (F.toPowerSeries j)) C t)) =
              Sum.elim (fun j => subst (Sum.elim A C) (F.toPowerSeries j)) B := by
            funext t
            rcases t with j | j
            · (try simp only [Sum.elim_inl, Sum.elim_inr])
              rw [rename_subst _ hAB]
              congr 1
              funext t'
              rcases t' with j' | j'
              · (try simp only [Sum.elim_inl, Sum.elim_inr]); exact hσA j'
              · (try simp only [Sum.elim_inl, Sum.elim_inr]); exact hσB j'
            · (try simp only [Sum.elim_inl, Sum.elim_inr]); exact hσC j
          have hR : (Sum.elim (fun j => subst (Sum.elim A B) (F.toPowerSeries j)) C) =
              Sum.elim (fun j => subst (Sum.elim A B) (F.toPowerSeries j)) C := rfl
          rw [hG3, rename_subst _ hT, hL, MvFormalGroup.subst_elim_assoc F hA0 hC0 hB0,
            MvFormalGroup.subst_elim_assoc F hA0 hB0 hC0]
          have hBC : (fun j => subst (Sum.elim C B) (F.toPowerSeries j)) = fun j => subst (Sum.elim B C) (F.toPowerSeries j) :=
            funext fun j => MvFormalGroup.subst_elim_comm F hC0 hB0 j
          rw [hBC]

end Perm
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

section Colsum

variable {n d : ℕ}

private theorem mapDomain_snd_apply (e : Fin n × Fin d →₀ ℕ) (j : Fin d) :
    Finsupp.mapDomain Prod.snd e j = ∑ s : Fin n, e (s, j) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun a => Finsupp.single_zero a.2), Finsupp.finsetSum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' Finset.univ j (fun y => e (s, y)), if_pos (Finset.mem_univ j)]

variable (i : Fin d)

private def expo {N : ℕ} (a : Fin n → Fin N) : Fin n × Fin d →₀ ℕ := ∑ s : Fin n, Finsupp.single (s, i) (a s : ℕ)

private theorem expo_apply {N : ℕ} (a : Fin n → Fin N) (t : Fin n) (j : Fin d) :
    expo i a (t, j) = if i = j then (a t : ℕ) else 0 := by
  classical
  rw [expo, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : i = j
  · subst h
    simp only [and_true, if_true]
    rw [Finset.sum_ite_eq' Finset.univ t (fun s => (a s : ℕ)), if_pos (Finset.mem_univ t)]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun s _ => if_neg fun h' => h h'.2

private theorem mapDomain_snd_expo {N : ℕ} (a : Fin n → Fin N) :
    Finsupp.mapDomain Prod.snd (expo i a) = Finsupp.single i (∑ s, (a s : ℕ)) := by
  classical
  ext j
  rw [mapDomain_snd_apply, Finsupp.single_apply]
  simp_rw [expo_apply]
  by_cases h : i = j
  · simp only [if_pos h]
  · simp only [if_neg h, Finset.sum_const_zero]

private theorem expo_comp_perm {N : ℕ} (a : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
    expo i (a ∘ σ) = Finsupp.mapDomain (pm (d := d) σ.symm) (expo i a) := by
  classical
  rw [expo, expo, Finsupp.mapDomain_finsetSum]
  simp_rw [Finsupp.mapDomain_single]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, pm, Prod.map_apply, id_eq, Equiv.symm_apply_apply]

end Colsum
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

section Final

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
  (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
  (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
  (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
    subst (Sum.elim
      (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
        MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
      (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
      (F.toPowerSeries k))

omit [F.IsComm] in
include hG1 hGsucc in

private theorem coeff_nthSeries_eq_sum (m : ℕ) (k i : Fin d) :
    (F.nthSeries (m + 1) k).coeff (Finsupp.single i (m + 1)) =
      ∑ a ∈ (Finset.univ : Finset (Fin (m + 1) → Fin (m + 2))).filter (fun a => ∑ s, (a s : ℕ) = m + 1),
        (G (m + 1) k).coeff (expo i a) := by
  classical
  rw [← rename_snd_G F G hG1 hGsucc m k, coeff_rename]

  have hmem : ∀ e : Fin (m + 1) × Fin d →₀ ℕ,
      e ∈ (Filter.TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain (Prod.snd : Fin (m + 1) × Fin d → Fin d))
        (Finsupp.single i (m + 1))).toFinset ↔ ∀ j, ∑ s, e (s, j) = if i = j then m + 1 else 0 := by
    intro e
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finsupp.ext_iff]
    refine forall_congr' fun j => ?_
    rw [mapDomain_snd_apply, Finsupp.single_apply]
  symm
  refine Finset.sum_bij' (fun a _ => expo i a) (fun e _ s => ⟨min (e (s, i)) (m + 1), by omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, mapDomain_snd_expo, ha.2]
  · intro e he
    rw [hmem] at he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hi := he i
    rw [if_pos rfl] at hi
    conv_rhs => rw [← hi]
    refine Finset.sum_congr rfl fun s _ => ?_
    change min (e (s, i)) (m + 1) = e (s, i)
    exact min_eq_left ((Finset.single_le_sum (f := fun s => e (s, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)).trans hi.le)
  · intro a ha
    funext s
    apply Fin.ext
    change min (expo i a (s, i)) (m + 1) = (a s : ℕ)
    rw [expo_apply, if_pos rfl]
    exact min_eq_left (Nat.le_of_lt_succ (a s).2)
  · intro e he
    rw [hmem] at he
    ext ⟨t, j⟩
    rw [expo_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      change min (e (t, i)) (m + 1) = e (t, i)
      have hj := he i
      rw [if_pos rfl] at hj
      exact min_eq_left ((Finset.single_le_sum (f := fun s => e (s, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans hj.le)
    · rw [if_neg h]
      have hj := he j
      rw [if_neg h] at hj
      exact ((Finset.sum_eq_zero_iff.1 hj) t (Finset.mem_univ t)).symm
  · intro a _
    rfl

include hG1 hGsucc in

private theorem main (m : ℕ) [hp : Fact (m + 1).Prime] (k i : Fin d) :
    (G (m + 1) k).coeff (∑ s : Fin (m + 1), Finsupp.single (s, i) 1) -
        (F.nthSeries (m + 1) k).coeff (Finsupp.single i (m + 1)) ∈ Ideal.span {((m + 1 : ℕ) : 𝓞)} := by
  classical
  set H := G (m + 1) k with hH
  set I : Ideal 𝓞 := Ideal.span {((m + 1 : ℕ) : 𝓞)} with hI
  rw [coeff_nthSeries_eq_sum F G hG1 hGsucc m k i]
  refine Ideal.Quotient.eq.1 ?_
  rw [map_sum]

  let g : (Fin (m + 1) → Fin (m + 2)) → 𝓞 ⧸ I := fun a =>
    if ∑ s, (a s : ℕ) = m + 1 then Ideal.Quotient.mk I (H.coeff (expo i a)) else 0
  have hM : ∀ x : 𝓞 ⧸ I, (m + 1) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) (m + 1), ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  have hg : ∀ (σ : Equiv.Perm (Fin (m + 1))) (a : Fin (m + 1) → Fin (m + 2)), g (a ∘ σ) = g a := by
    intro σ a
    have hs : ∑ s, ((a ∘ σ) s : ℕ) = ∑ s, (a s : ℕ) := Equiv.sum_comp σ (fun s => (a s : ℕ))
    have hcoeff : H.coeff (expo i (a ∘ σ)) = H.coeff (expo i a) := by
      let ε : (Fin (m + 1) × Fin d) ↪ (Fin (m + 1) × Fin d) := (Equiv.prodCongr σ.symm (Equiv.refl (Fin d))).toEmbedding
      have hε : (ε : Fin (m + 1) × Fin d → Fin (m + 1) × Fin d) = pm σ.symm := by
        funext ⟨s, j⟩; rfl
      rw [expo_comp_perm, ← hε, ← Finsupp.embDomain_eq_mapDomain]
      conv_lhs => rw [hH, ← rename_pm_G F G hG1 hGsucc m σ.symm k, ← hH, rename_congr hε.symm]
      exact coeff_embDomain_rename ε H (expo i a)
    simp only [g, hs, hcoeff]
  have horbit := HNAOrbit.sum_eq_sum_const_fin (m + 1) hM g hg

  have hconst : ∑ c : Fin (m + 2), g (fun _ => c) =
      Ideal.Quotient.mk I (H.coeff (∑ s : Fin (m + 1), Finsupp.single (s, i) 1)) := by
    rw [Finset.sum_eq_single (1 : Fin (m + 2))]
    · have h1 : ∑ _s : Fin (m + 1), ((1 : Fin (m + 2)) : ℕ) = m + 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fin.val_one, smul_eq_mul, mul_one]
      have h2 : expo i (fun _ : Fin (m + 1) => (1 : Fin (m + 2))) = ∑ s : Fin (m + 1), Finsupp.single (s, i) 1 := by
        simp only [expo, Fin.val_one]
      simp only [g, h1, if_true, h2]
    · intro c _ hc
      have hne : ∑ _s : Fin (m + 1), (c : ℕ) ≠ m + 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        intro h
        apply hc
        apply Fin.ext
        rw [Fin.val_one]
        have : (c : ℕ) = 1 := by
          rcases Nat.lt_or_ge (c : ℕ) 1 with h0 | h1
          · have : (c : ℕ) = 0 := by omega
            rw [this, mul_zero] at h; omega
          · rcases Nat.eq_or_lt_of_le h1 with h1 | h2
            · exact h1.symm
            · have : (m + 1) * 2 ≤ (m + 1) * (c : ℕ) := Nat.mul_le_mul_left _ h2
              omega
        exact this
      simp only [g, hne, if_false]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hfilter : ∑ a ∈ (Finset.univ : Finset (Fin (m + 1) → Fin (m + 2))).filter (fun a => ∑ s, (a s : ℕ) = m + 1),
      Ideal.Quotient.mk I (H.coeff (expo i a)) = ∑ a, g a := by
    rw [Finset.sum_filter]
  rw [hfilter, horbit, hconst]

end Final
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit"

end HNABody
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNABody"

open HNABody in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
    (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
    (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k))
    (k i : Fin d) :
    (G p k).coeff (∑ s : Fin p, Finsupp.single (s, i) 1) -
        (F.nthSeries p k).coeff (Finsupp.single i p) ∈ Ideal.span {(p : 𝓞)} := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm⟩
  exact main F G hG1 hGsucc m k i

end
p2m_reactivate "P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit.Tup P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNAOrbit P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span.HNABody"

end S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span
end P2MW
export P2MW.S_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span (solution)
