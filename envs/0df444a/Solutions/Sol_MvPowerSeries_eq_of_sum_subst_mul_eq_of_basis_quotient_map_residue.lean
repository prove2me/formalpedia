-- Prove2me | solution 1 for MvPowerSeries.eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d04901e5-9e7b-5835-aa52-bdf84d7f9503

import Mathlib
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open MvPowerSeries IsLocalRing

namespace K2Free

variable {B : Type*} [CommRing B]

section CoeffIn

variable {σ : Type*}

def CoeffIn (I : Ideal B) (f : MvPowerSeries σ B) : Prop := ∀ d : σ →₀ ℕ, coeff d f ∈ I

theorem CoeffIn.top (f : MvPowerSeries σ B) : CoeffIn ⊤ f := fun _ => Submodule.mem_top

theorem CoeffIn.mono {I J : Ideal B} (h : I ≤ J) {f : MvPowerSeries σ B} (hf : CoeffIn I f) : CoeffIn J f :=
  fun d => h (hf d)

theorem CoeffIn.zero (I : Ideal B) : CoeffIn I (0 : MvPowerSeries σ B) := fun d => by
  rw [map_zero]; exact I.zero_mem

theorem CoeffIn.add {I : Ideal B} {f g : MvPowerSeries σ B} (hf : CoeffIn I f) (hg : CoeffIn I g) :
    CoeffIn I (f + g) := fun d => by
  rw [map_add]; exact I.add_mem (hf d) (hg d)

theorem CoeffIn.sum {I : Ideal B} {κ : Type*} (s : Finset κ) {f : κ → MvPowerSeries σ B}
    (hf : ∀ l ∈ s, CoeffIn I (f l)) : CoeffIn I (∑ l ∈ s, f l) := fun d => by
  rw [map_sum]; exact I.sum_mem fun l hl => hf l hl d

theorem CoeffIn.smul {I : Ideal B} (r : B) {f : MvPowerSeries σ B} (hf : CoeffIn I f) : CoeffIn I (r • f) :=
  fun d => by rw [map_smul, smul_eq_mul]; exact I.mul_mem_left r (hf d)

theorem CoeffIn.smul_mem {I J : Ideal B} {r : B} (hr : r ∈ J) {f : MvPowerSeries σ B} (hf : CoeffIn I f) :
    CoeffIn (J * I) (r • f) :=
  fun d => by rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_mul hr (hf d)

theorem CoeffIn.mul_right {I : Ideal B} {f : MvPowerSeries σ B} (hf : CoeffIn I f) (g : MvPowerSeries σ B) :
    CoeffIn I (f * g) := fun d => by
  classical
  rw [coeff_mul]
  exact I.sum_mem fun p _ => I.mul_mem_right _ (hf p.1)

theorem CoeffIn.subst {τ : Type*} {a : σ → MvPowerSeries τ B} (ha : HasSubst a) {I : Ideal B}
    {f : MvPowerSeries σ B} (hf : CoeffIn I f) : CoeffIn I (subst a f) := fun e => by
  rw [coeff_subst ha f e]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) fun d => ?_
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (hf d)

theorem coeffIn_maximalIdeal_iff [IsLocalRing B] (f : MvPowerSeries σ B) :
    CoeffIn (maximalIdeal B) f ↔ map (residue B) f = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun d => ?_
  rw [coeff_map, coeff_zero, residue_eq_zero_iff]

theorem eq_zero_of_forall_coeffIn_pow [IsNoetherianRing B] [IsLocalRing B] (f : MvPowerSeries σ B)
    (h : ∀ j : ℕ, CoeffIn (maximalIdeal B ^ j) f) : f = 0 := by
  ext d
  rw [coeff_zero]
  have hmem : coeff d f ∈ ⨅ j : ℕ, maximalIdeal B ^ j := Ideal.mem_iInf.mpr fun j => h j d
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top, Ideal.mem_bot] at hmem

end CoeffIn

theorem exists_minimal_generators [IsNoetherianRing B] [IsLocalRing B] (I : Ideal B) :
    ∃ (s : ℕ) (b : Fin s → B), Ideal.span (Set.range b) = I ∧
      ∀ c : Fin s → B, ∑ l, c l * b l ∈ maximalIdeal B * I → ∀ l, c l ∈ maximalIdeal B := by
  classical
  have hex : ∃ s : ℕ, ∃ b : Fin s → B, Ideal.span (Set.range b) = I := by
    obtain ⟨s, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
    exact ⟨s, b, hb⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).choose, (Nat.find_spec hex).choose_spec, ?_⟩
  set s := Nat.find hex with hs
  set b : Fin s → B := (Nat.find_spec hex).choose with hb
  have hbI : Ideal.span (Set.range b) = I := (Nat.find_spec hex).choose_spec
  intro c hc
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀⟩ := hcon
  have hu : IsUnit (c l₀) := by
    by_contra h; exact hl₀ ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hu

  obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos (Fin.pos l₀)).symm⟩
  let ε : Fin (s' + 1) ≃ Fin s := finCongr hs'.symm
  let l₁ : Fin (s' + 1) := ε.symm l₀
  let b' : Fin s' → B := fun l => b (ε (l₁.succAbove l))
  have hb'I : Ideal.span (Set.range b') = I := by
    apply le_antisymm
    · rw [← hbI]
      exact Ideal.span_mono (by rintro _ ⟨l, rfl⟩; exact ⟨_, rfl⟩)
    ·
      have hle : (I : Submodule B B) ≤ Ideal.span (Set.range b') ⊔ maximalIdeal B • I := by
        suffices h : Ideal.span (Set.range b) ≤ Ideal.span (Set.range b') ⊔ maximalIdeal B • I by
          rwa [hbI] at h
        rw [Ideal.span_le]
        rintro _ ⟨l, rfl⟩
        by_cases hll : l = l₀
        · rw [hll]
          have hsplit : ∑ l, c l * b l = c l₀ * b l₀ + ∑ l, c (ε (l₁.succAbove l)) * b' l := by
            rw [← Equiv.sum_comp ε (fun l => c l * b l), Fin.sum_univ_succAbove _ l₁]
            simp [l₁, b']
          have heq : b l₀ = ↑u⁻¹ * (∑ l, c l * b l - ∑ l, c (ε (l₁.succAbove l)) * b' l) := by
            rw [hsplit, add_sub_cancel_right, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
          rw [heq]
          refine Ideal.mul_mem_left _ _ (Submodule.sub_mem _ ?_ ?_)
          · refine Submodule.mem_sup_right ?_
            rw [Ideal.smul_eq_mul]
            exact hc
          · refine Submodule.mem_sup_left (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_)
            exact Ideal.subset_span ⟨l, rfl⟩
        · refine Submodule.mem_sup_left (Ideal.subset_span ?_)
          obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq (x := ε.symm l) (y := l₁)
            (by intro h; exact hll (by simpa [l₁] using congrArg ε h))
          exact ⟨l', by simp [b', hl']⟩
      have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
        (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) hle
      exact hN
  have hmin := Nat.find_min hex (m := s') (by omega)
  exact hmin ⟨b', hb'I⟩

section Devissage

variable [IsNoetherianRing B] [IsLocalRing B] {σ τ ι : Type*} [Finite σ] [Fintype ι]

theorem eq_zero_of_sum_subst_mul_eq_zero_of_residue
    {a : σ → MvPowerSeries τ B} (ha0 : ∀ s, constantCoeff (a s) = 0) (e : ι → MvPowerSeries τ B)
    (hres : ∀ w : ι → MvPowerSeries σ (ResidueField B),
      ∑ i, subst (fun s => map (residue B) (a s)) (w i) * map (residue B) (e i) = 0 → w = 0)
    (c : ι → MvPowerSeries σ B) (hc : ∑ i, subst a (c i) * e i = 0) : c = 0 := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0

  let Ψ : (ι → MvPowerSeries σ B) →ₗ[B] MvPowerSeries τ B :=
    ∑ i, (LinearMap.mulRight B (e i)).comp ((substAlgHom ha).toLinearMap.comp (LinearMap.proj i))
  have hΨ : ∀ w : ι → MvPowerSeries σ B, Ψ w = ∑ i, subst a (w i) * e i := by
    intro w
    simp only [Ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply, substAlgHom_apply, LinearMap.mulRight_apply]

  have hΨres : ∀ w : ι → MvPowerSeries σ B,
      CoeffIn (maximalIdeal B) (Ψ w) → ∀ i, CoeffIn (maximalIdeal B) (w i) := by
    intro w hw i
    rw [coeffIn_maximalIdeal_iff] at hw ⊢
    rw [hΨ, map_sum] at hw
    simp only [map_mul, map_subst ha] at hw
    exact congrFun (hres (fun i => map (residue B) (w i)) hw) i

  have main : ∀ t : ℕ, ∀ i, CoeffIn (maximalIdeal B ^ t) (c i) := by
    intro t
    induction t with
    | zero => intro i; rw [pow_zero, Ideal.one_eq_top]; exact CoeffIn.top _
    | succ t ih =>
      obtain ⟨s, g, hgI, hgind⟩ := exists_minimal_generators (maximalIdeal B ^ t)
      have hgl : ∀ l, g l ∈ maximalIdeal B ^ t := fun l => by
        rw [← hgI]; exact Ideal.subset_span ⟨l, rfl⟩

      have hdec : ∀ (i : ι) (d : σ →₀ ℕ), ∃ γ : Fin s → B, ∑ l, γ l • g l = coeff d (c i) := by
        intro i d
        have h := ih i d
        rw [← hgI] at h
        exact (Submodule.mem_span_range_iff_exists_fun B).mp h
      choose γ hγ using hdec
      let w : Fin s → ι → MvPowerSeries σ B := fun l i => fun d => γ i d l
      have hw : ∀ l i (d : σ →₀ ℕ), coeff d (w l i) = γ i d l := fun _ _ _ => rfl
      have hcw : c = ∑ l, g l • w l := by
        funext i; ext d
        rw [← hγ i d, Finset.sum_apply, map_sum]
        simp only [Pi.smul_apply, map_smul, hw, smul_eq_mul, mul_comm]

      have hsum : ∑ l, g l • Ψ (w l) = 0 := by
        have : Ψ c = 0 := by rw [hΨ]; exact hc
        rw [← this, hcw, map_sum]
        simp only [map_smul]

      have hwm : ∀ l, CoeffIn (maximalIdeal B) (Ψ (w l)) := by
        intro l d
        have h1 : ∑ l, coeff d (Ψ (w l)) * g l ∈ maximalIdeal B * maximalIdeal B ^ t := by
          have h2 : ∑ l, coeff d (Ψ (w l)) * g l = coeff d (∑ l, g l • Ψ (w l)) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul, mul_comm]
          rw [h2, hsum, map_zero]
          exact Ideal.zero_mem _
        exact hgind _ h1 l
      intro i
      rw [congrFun hcw i, Finset.sum_apply, pow_succ]
      refine CoeffIn.sum _ fun l _ => ?_
      rw [Pi.smul_apply]
      exact CoeffIn.smul_mem (hgl l) (hΨres _ (hwm l) i)
  funext i
  exact eq_zero_of_forall_coeffIn_pow _ fun t => main t i

end Devissage

end K2Free

open MvPowerSeries IsLocalRing

namespace K2Free

universe u

namespace FieldCase

variable {k : Type u} [Field k] {n : ℕ}

def Tgt (_φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) : Type u := MvPowerSeries (Fin n) k

noncomputable scoped instance (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) : CommRing (Tgt φ) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin n) k))

def toTgt (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) : MvPowerSeries (Fin n) k →+* Tgt φ := φ

noncomputable scoped instance (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) :
    Algebra (MvPowerSeries (Fin n) k) (Tgt φ) := (toTgt φ).toAlgebra

noncomputable def ofT (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) :
    Tgt φ ≃+* MvPowerSeries (Fin n) k := RingEquiv.refl _

theorem ofT_algebraMap (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) (r : MvPowerSeries (Fin n) k) :
    ofT φ (algebraMap (MvPowerSeries (Fin n) k) (Tgt φ) r) = φ r := rfl

theorem ofT_smul (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) (r : MvPowerSeries (Fin n) k)
    (t : Tgt φ) : ofT φ (r • t) = φ r * ofT φ t := by
  rw [Algebra.smul_def, map_mul, ofT_algebraMap]

scoped instance (φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k) : IsLocalRing (Tgt φ) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries (Fin n) k))

end FieldCase
p2m_reactivate "P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.K2Free.FieldCase"

open FieldCase in

theorem eq_zero_of_sum_subst_mul_eq_zero_field {k : Type u} [Field k] {n d : ℕ}
    (g : Fin n → MvPowerSeries (Fin n) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (e : Fin d → MvPowerSeries (Fin n) k)
    (β : Module.Basis (Fin d) k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)))
    (hβ : ∀ j, β j = Ideal.Quotient.mk (Ideal.span (Set.range g)) (e j))
    (w : Fin d → MvPowerSeries (Fin n) k) (hw : ∑ j, subst g (w j) * e j = 0) : w = 0 := by
  classical
  haveI : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)) := Module.Finite.of_basis β
  obtain ⟨hfinT, -, b₀, hb₀⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient g hg inferInstance

  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg
  let φa : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) k := substAlgHom (R := k) hgs
  let φ : MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin n) k := φa.toRingHom
  have hφ : ∀ x, φ x = subst g x := fun x => by
    show φa x = _
    rw [coe_substAlgHom]
  have hφC : ∀ c : k, φ (C c) = C c := fun c => by
    show φa (C c) = _
    rw [c_eq_algebraMap, AlgHom.commutes]
  let S := MvPowerSeries (Fin n) k
  let T := Tgt φ
  let ε : T ≃+* MvPowerSeries (Fin n) k := ofT φ
  have hε_smul : ∀ (r : S) (t : T), ε (r • t) = φ r * ε t := ofT_smul φ
  have hε_symm : ∀ x, ε (ε.symm x) = x := fun x => rfl

  haveI hfinM : Module.Finite S T := hfinT

  have hr : Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g)) = d := by
    rw [Module.finrank_eq_card_basis β, Fintype.card_fin]

  let L₀ : (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g))) → S) →ₗ[S] T :=
    Fintype.linearCombination S (fun i => ε.symm (b₀ i))
  have hL₀ : ∀ c, ε (L₀ c) = ∑ i, subst g (c i) * b₀ i := by
    intro c
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [hε_smul, hε_symm, hφ]
  have hL₀bij : Function.Bijective L₀ := by
    constructor
    · intro c c' h
      exact (hb₀ (ε (L₀ c))).unique (hL₀ c) (by rw [h, hL₀])
    · intro t
      obtain ⟨c, hc, -⟩ := hb₀ (ε t)
      exact ⟨c, ε.injective (by rw [hL₀, ← hc])⟩
  let E₀ : (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range g))) → S) ≃ₗ[S] T :=
    LinearEquiv.ofBijective L₀ hL₀bij

  let L : (Fin d → S) →ₗ[S] T := Fintype.linearCombination S (fun j => ε.symm (e j))
  have hL : ∀ w, ε (L w) = ∑ j, subst g (w j) * e j := by
    intro w
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [hε_smul, hε_symm, hφ]

  have hX : ∀ i : Fin n, (X i : S) ∈ maximalIdeal S := fun i => by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X, isUnit_iff_ne_zero]
    exact fun h => h rfl
  have hgm : ∀ y ∈ Ideal.span (Set.range g), ε.symm y ∈ (maximalIdeal S • ⊤ : Submodule S T) := by
    intro y hy
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have hle : Ideal.map (ε.symm : MvPowerSeries (Fin n) k →+* T) (Ideal.span (Set.range g)) ≤
        Ideal.map (algebraMap S T) (maximalIdeal S) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have : (ε.symm : MvPowerSeries (Fin n) k →+* T) (g i) = algebraMap S T (X i) := by
        apply ε.injective
        show ε (ε.symm (g i)) = ε (algebraMap S T (X i))
        rw [hε_symm, ofT_algebraMap, hφ, subst_X hgs]
      rw [this]
      exact Ideal.mem_map_of_mem _ (hX i)
    exact hle (Ideal.mem_map_of_mem _ hy)

  have hspan : (⊤ : Submodule S T) ≤ Submodule.span S (Set.range fun j => ε.symm (e j)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) ?_
    rintro t -

    let x : MvPowerSeries (Fin n) k := ε t
    have hx : Ideal.Quotient.mk (Ideal.span (Set.range g)) x =
        Ideal.Quotient.mk (Ideal.span (Set.range g)) (∑ j, C (β.repr (Ideal.Quotient.mk _ x) j) * e j) := by
      conv_lhs => rw [← β.sum_repr (Ideal.Quotient.mk (Ideal.span (Set.range g)) x)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, ← smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hx
    have ht : t = (∑ j, (C (β.repr (Ideal.Quotient.mk _ x) j) : S) • ε.symm (e j)) +
        ε.symm (x - ∑ j, C (β.repr (Ideal.Quotient.mk _ x) j) * e j) := by
      apply ε.injective
      rw [map_add, map_sum, hε_symm]
      simp only [hε_smul, hε_symm, hφC]
      show ε t = _
      ring
    rw [ht]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))) (Submodule.mem_sup_right (hgm _ hx))
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact top_le_iff.mp hspan

  let G : T ≃ₗ[S] (Fin d → S) :=
    E₀.symm.trans (LinearEquiv.funCongrLeft S S (finCongr hr).symm)
  have hF : Function.Injective (G.toLinearMap.comp L) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (G.surjective.comp hLsurj)
  have hLinj : Function.Injective L := by
    rw [LinearMap.coe_comp] at hF
    exact hF.of_comp

  have hLw : L w = 0 := ε.injective (by rw [hL, hw, map_zero])
  exact hLinj (hLw.trans (map_zero L).symm)

end K2Free
p2m_reactivate "P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.K2Free.FieldCase P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.K2Free"

open MvPowerSeries IsLocalRing in
theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (MvPowerSeries (Fin n) (IsLocalRing.ResidueField B) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i))))
    (hβ : ∀ j, β j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue B) (b j)))
    (c c' : Fin d → MvPowerSeries (Fin n) B)
    (h : ∑ j, MvPowerSeries.subst ρ (c j) * b j = ∑ j, MvPowerSeries.subst ρ (c' j) * b j) : c = c' := by
  have hρ : MvPowerSeries.HasSubst ρ := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  have h0 : ∑ j, MvPowerSeries.subst ρ ((c - c') j) * b j = 0 := by
    simp only [Pi.sub_apply, MvPowerSeries.subst_sub hρ, sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hres : ∀ w : Fin d → MvPowerSeries (Fin n) (ResidueField B),
      ∑ i, subst (fun s => map (residue B) (ρ s)) (w i) * map (residue B) (b i) = 0 → w = 0 :=
    fun w hw => K2Free.eq_zero_of_sum_subst_mul_eq_zero_field (fun i => map (residue B) (ρ i))
      (fun i => by rw [constantCoeff_map, hρ0, map_zero]) (fun j => map (residue B) (b j)) β hβ w hw
  exact sub_eq_zero.mp (K2Free.eq_zero_of_sum_subst_mul_eq_zero_of_residue hρ0 b hres (c - c') h0)

end S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
end P2MW
export P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue (solution)
