-- Prove2me | solution 1 for MasulloGRH.sZetaIntegral_integrable_and_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:59:16.218459+00:00
-- url     : https://prove2.me/submissions/c1bdcb48-e7ab-4073-b68e-d4cd88c88b1b

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_MasulloGRH_correspondence_growth_bound
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# Convergence and holomorphy of the `S`-local zeta integrals

* `decays_schwartz`: an `S`-adelic Schwartz–Bruhat function is continuous, vanishes outside a box
  `‖x_v‖ ≤ R` at the finite places, and decays faster than any power of `∑_{w ∣ ∞} ‖x_w‖`.  For a
  generator `extendPullback Γ π g` this uses that `Γ` is compactly generated (finite places),
  that the good subgroup `k` is compact (`MasulloGRH.isCompact_of_isGoodSubgroup`), the linear
  growth bound `MasulloGRH.correspondence_growth_bound` and the rapid decay of `g`
  (`MasulloGRH.isRapidDecay_elemSchwartz_toFun`).
* `integrable_norm_mul_rpow`: `‖f‖ |·|_{F,S}^σ` is `μ_S`-integrable for `σ > 0`, by a product
  majorant and Tonelli; the local factors are finite (`arch_local_lintegral`,
  `finite_local_add_lintegral`).
* `solution`: integrability and holomorphy (differentiation under the integral sign).

The argument follows the proof in the open formalization mccorvie/riemann-masullo.
-/

namespace Sol_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn
open MasulloGRH Topology

section Elem
variable {m n r s : ℕ} {d : Fin s → ℕ}

theorem elem_continuous (g : ElemSchwartz m n r s d) : Continuous g.toFun := by
  have hg := isRapidDecay_elemSchwartz_toFun g
  let q : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.id.prodMap
      ((IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).prodMap
        IsOpenQuotientMap.id)
  refine hq.isQuotientMap.continuous_iff.mpr ?_
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, t0, a0, b0⟩
  have hnhds : {p : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) |
      p.2.2 = (a0, b0)} ∈ 𝓝 (x0, t0, a0, b0) :=
    ((isOpen_discrete {(a0, b0)}).preimage (continuous_snd.comp continuous_snd)).mem_nhds rfl
  have hc : ContinuousAt (fun p : (Fin m → ℝ) × (Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) =>
      elemLift g.toFun a0 b0 (p.1, p.2.1)) (x0, t0, a0, b0) :=
    ((hg.1 a0 b0).continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousAt
  refine hc.congr (Filter.mem_of_superset hnhds fun p hp => ?_)
  obtain ⟨x, t, a, b⟩ := p
  simp only [Set.mem_setOf_eq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

theorem elem_decay (g : ElemSchwartz m n r s d) (N : ℕ) : ∃ C : ℝ, ∀ e : ElemGroup m n r s d,
    ‖g.toFun e‖ * (1 + (‖e.1‖ + ‖e.2.2.1‖)) ^ N ≤ C := by
  have hg := isRapidDecay_elemSchwartz_toFun g
  obtain ⟨C0, hC0⟩ := hg.2 0 0 0
  obtain ⟨C1, hC1⟩ := hg.2 N 0 0
  obtain ⟨C2, hC2⟩ := hg.2 0 N 0
  refine ⟨3 ^ N * max C0 (max C1 C2), fun e => ?_⟩
  obtain ⟨x, z, a, b⟩ := e
  choose t ht using fun j => QuotientAddGroup.mk_surjective (z j)
  have hz : z = fun j => ((t j : ℝ) : UnitAddCircle) := funext fun j => (ht j).symm
  subst hz
  have hval : g.toFun (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b) =
      elemLift g.toFun a b (x, t) := rfl
  have h0 := hC0 a b (x, t)
  have h1 := hC1 a b (x, t)
  have h2 := hC2 a b (x, t)
  simp only [pow_zero, one_mul, mul_one, norm_iteratedFDeriv_zero] at h0 h1 h2
  rw [← hval] at h0 h1 h2
  simp only
  set u := ‖g.toFun (x, fun j => ((t j : ℝ) : UnitAddCircle), a, b)‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  set M := max 1 (max ‖x‖ ‖a‖) with hM
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hle : 1 + (‖x‖ + ‖a‖) ≤ 3 * M := by
    have := le_max_left 1 (max ‖x‖ ‖a‖)
    have := le_max_left ‖x‖ ‖a‖
    have := le_max_right ‖x‖ ‖a‖
    have := le_max_right 1 (max ‖x‖ ‖a‖)
    linarith
  have hpow : (1 + (‖x‖ + ‖a‖)) ^ N ≤ 3 ^ N * M ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  have hkey : u * M ^ N ≤ max C0 (max C1 C2) := by
    rcases max_choice 1 (max ‖x‖ ‖a‖) with h | h
    · rw [hM, h, one_pow, mul_one]; exact h0.trans (le_max_left _ _)
    · rw [hM, h]
      rcases max_choice ‖x‖ ‖a‖ with h' | h'
      · rw [h', mul_comm]; exact h1.trans ((le_max_left _ _).trans (le_max_right _ _))
      · rw [h', mul_comm]; exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  calc u * (1 + (‖x‖ + ‖a‖)) ^ N ≤ u * (3 ^ N * M ^ N) := mul_le_mul_of_nonneg_left hpow hu0
    _ = 3 ^ N * (u * M ^ N) := by ring
    _ ≤ 3 ^ N * max C0 (max C1 C2) := mul_le_mul_of_nonneg_left hkey (by positivity)

end Elem

section SAdele
variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

instance instT2Mult : T2Space (Multiplicative (SAdeleRing F Sf)) :=
  inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
    ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))

instance instLCMult : LocallyCompactSpace (Multiplicative (SAdeleRing F Sf)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  infer_instance

/-- The size `∑_{w ∣ ∞} ‖x_w‖` of the archimedean part of an `S`-adele. -/
noncomputable def archSize (x : SAdeleRing F Sf) : ℝ := ∑ w : InfinitePlace F, ‖x.1 w‖

theorem archSize_nonneg (x : SAdeleRing F Sf) : 0 ≤ archSize x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

variable (Sf) in
/-- Continuity, support in a box at the finite places, and rapid decay at the archimedean
places. -/
def Decays (h : Multiplicative (SAdeleRing F Sf) → ℂ) : Prop :=
  Continuous h ∧
  (∃ R : ℝ, ∀ x : SAdeleRing F Sf, (∃ v : Sf, R < ‖x.2 v‖) → h (Multiplicative.ofAdd x) = 0) ∧
  ∀ N : ℕ, ∃ B : ℝ, ∀ x : SAdeleRing F Sf,
    ‖h (Multiplicative.ofAdd x)‖ * (1 + archSize x) ^ N ≤ B

theorem decays_zero : Decays Sf (0 : Multiplicative (SAdeleRing F Sf) → ℂ) :=
  ⟨continuous_const, ⟨0, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩

theorem decays_add {h₁ h₂ : Multiplicative (SAdeleRing F Sf) → ℂ} (h1 : Decays Sf h₁)
    (h2 : Decays Sf h₂) : Decays Sf (h₁ + h₂) := by
  obtain ⟨c1, ⟨R1, hR1⟩, d1⟩ := h1
  obtain ⟨c2, ⟨R2, hR2⟩, d2⟩ := h2
  refine ⟨c1.add c2, ⟨max R1 R2, fun x ⟨v, hv⟩ => ?_⟩, fun N => ?_⟩
  · simp only [Pi.add_apply]
    rw [hR1 x ⟨v, lt_of_le_of_lt (le_max_left _ _) hv⟩,
      hR2 x ⟨v, lt_of_le_of_lt (le_max_right _ _) hv⟩, add_zero]
  · obtain ⟨B1, hB1⟩ := d1 N
    obtain ⟨B2, hB2⟩ := d2 N
    refine ⟨B1 + B2, fun x => ?_⟩
    have hp : 0 ≤ (1 + archSize x) ^ N := pow_nonneg (by linarith [archSize_nonneg x]) N
    calc ‖(h₁ + h₂) (Multiplicative.ofAdd x)‖ * (1 + archSize x) ^ N
        ≤ (‖h₁ (Multiplicative.ofAdd x)‖ + ‖h₂ (Multiplicative.ofAdd x)‖) *
            (1 + archSize x) ^ N := mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
      _ ≤ B1 + B2 := by rw [add_mul]; exact add_le_add (hB1 x) (hB2 x)

theorem decays_smul (a : ℂ) {h : Multiplicative (SAdeleRing F Sf) → ℂ} (h1 : Decays Sf h) :
    Decays Sf (a • h) := by
  obtain ⟨c1, ⟨R1, hR1⟩, d1⟩ := h1
  refine ⟨c1.const_smul a, ⟨R1, fun x hx => ?_⟩, fun N => ?_⟩
  · simp [hR1 x hx]
  · obtain ⟨B1, hB1⟩ := d1 N
    refine ⟨‖a‖ * B1, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB1 x) (norm_nonneg a)

/-- The real coordinates `(part (ι_w x_w))_w` of the archimedean part, indexed by `Fin #S_∞`. -/
noncomputable def archCoord (part : ℂ →L[ℝ] ℝ) (x : SAdeleRing F Sf) :
    Fin (Fintype.card (InfinitePlace F)) → ℝ :=
  fun j => part (InfinitePlace.Completion.extensionEmbedding _
    (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)))

theorem continuous_archCoord (part : ℂ →L[ℝ] ℝ) :
    Continuous (archCoord (Sf := Sf) part) :=
  continuous_pi fun j => part.continuous.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp
      ((continuous_apply _).comp continuous_fst))

/-- `archCoord` as an additive map. -/
noncomputable def archCoordHom (part : ℂ →L[ℝ] ℝ) :
    SAdeleRing F Sf →+ (Fin (Fintype.card (InfinitePlace F)) → ℝ) where
  toFun := archCoord part
  map_zero' := by
    funext j
    change part (InfinitePlace.Completion.extensionEmbedding _ (0 : _)) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    funext j
    change part (InfinitePlace.Completion.extensionEmbedding _
      (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j) +
        y.1 ((Fintype.equivFin (InfinitePlace F)).symm j))) = _
    rw [map_add, map_add]
    rfl

/-- `archCoord` as a continuous homomorphism to an elementary group. -/
noncomputable def archCoordElem (part : ℂ →L[ℝ] ℝ) :
    Multiplicative (SAdeleRing F Sf) →*
      Multiplicative (ElemGroup (Fintype.card (InfinitePlace F)) 0 0 0 Fin.elim0) :=
  AddMonoidHom.toMultiplicative ((archCoordHom (Sf := Sf) part).prod 0)

theorem continuous_archCoordElem (part : ℂ →L[ℝ] ℝ) :
    Continuous (archCoordElem (Sf := Sf) part) := by
  change Continuous fun x : Multiplicative (SAdeleRing F Sf) =>
    Multiplicative.ofAdd ((archCoord part (Multiplicative.toAdd x),
      (0 : (Fin 0 → UnitAddCircle) × (Fin 0 → ℤ) × ((i : Fin 0) → ZMod (Fin.elim0 i)))))
  exact continuous_ofAdd.comp (((continuous_archCoord part).comp continuous_toAdd).prodMk
    continuous_const)

theorem norm_le_archCoord (x : SAdeleRing F Sf) (j : Fin (Fintype.card (InfinitePlace F))) :
    ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖ ≤
      ‖archCoord Complex.reCLM x‖ + ‖archCoord Complex.imCLM x‖ := by
  have h1 : ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖ =
      ‖InfinitePlace.Completion.extensionEmbedding _
        (x.1 ((Fintype.equivFin (InfinitePlace F)).symm j))‖ :=
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero
      (map_zero _) _).symm
  have hre := norm_le_pi_norm (archCoord (Sf := Sf) Complex.reCLM x) j
  have him := norm_le_pi_norm (archCoord (Sf := Sf) Complex.imCLM x) j
  simp only [archCoord, Complex.reCLM_apply, Complex.imCLM_apply,
    Real.norm_eq_abs] at hre him
  rw [h1]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

theorem decays_extendPullback {m n r s : ℕ} {d : Fin s → ℕ}
    (Γ k : Subgroup (Multiplicative (SAdeleRing F Sf)))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g : ElemSchwartz m n r s d)
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    Decays Sf (extendPullback Γ π g.toFun) := by
  classical
  have hΓo : IsOpen (Γ : Set (Multiplicative (SAdeleRing F Sf))) := hs.1
  have hΓc : IsClosed (Γ : Set (Multiplicative (SAdeleRing F Sf))) :=
    Subgroup.isClosed_of_isOpen Γ hΓo
  have hval : ∀ y : Γ, extendPullback Γ π g.toFun y = g.toFun (Multiplicative.toAdd (π y)) :=
    fun y => by simp [extendPullback, y.2]
  have hzero : ∀ y, y ∉ Γ → extendPullback Γ π g.toFun y = 0 :=
    fun y hy => by simp [extendPullback, hy]
  refine ⟨?_, ?_, ?_⟩
  · -- continuity
    have hφ : Continuous (fun y : Γ => g.toFun (Multiplicative.toAdd (π y))) :=
      (elem_continuous g).comp (continuous_toAdd.comp hπ.2.1)
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Γ
    · have he : IsOpenEmbedding (Subtype.val : Γ → Multiplicative (SAdeleRing F Sf)) :=
        hΓo.isOpenEmbedding_subtypeVal
      have h1 : extendPullback Γ π g.toFun ∘ Subtype.val =
          fun y : Γ => g.toFun (Multiplicative.toAdd (π y)) := funext hval
      have h2 := (he.continuousAt_iff (g := extendPullback Γ π g.toFun) (x := ⟨x, hx⟩)).mp
        (h1 ▸ hφ.continuousAt)
      exact h2
    · have : extendPullback Γ π g.toFun =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hΓc.isOpen_compl.mem_nhds hx] with y hy
        exact hzero y hy
      exact continuousAt_const.congr this.symm
  · -- support
    obtain ⟨U, hUc, hUΓ, -, hUgen⟩ := hs.2.1
    have hcontφ : Continuous (fun x : Multiplicative (SAdeleRing F Sf) =>
        ∑ v : Sf, ‖(Multiplicative.toAdd x).2 v‖) :=
      continuous_finsetSum _ fun v _ =>
        ((continuous_apply v).comp (continuous_snd.comp continuous_toAdd)).norm
    obtain ⟨R0, hR0⟩ := hUc.exists_bound_of_continuousOn hcontφ.continuousOn
    set R := max R0 0 with hR
    let H : Subgroup (Multiplicative (SAdeleRing F Sf)) :=
      { carrier := {x | ∀ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ ≤ R}
        mul_mem' := fun {a b} ha hb v => by
          simp only [Set.mem_setOf_eq, toAdd_mul, Prod.snd_add, Pi.add_apply] at ha hb ⊢
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha v) (hb v))
        one_mem' := fun v => by simp [hR]
        inv_mem' := fun {a} ha v => by simpa using ha v }
    have hUH : U ⊆ H := fun x hx v => by
      have h1 := hR0 x hx
      rw [Real.norm_eq_abs] at h1
      have h2 : ‖(Multiplicative.toAdd x).2 v‖ ≤ ∑ v : Sf, ‖(Multiplicative.toAdd x).2 v‖ :=
        Finset.single_le_sum (f := fun v : Sf => ‖(Multiplicative.toAdd x).2 v‖)
          (fun v _ => norm_nonneg _) (Finset.mem_univ v)
      exact h2.trans ((le_abs_self _).trans (h1.trans (le_max_left _ _)))
    have hΓH : Γ ≤ H := hUgen ▸ (Subgroup.closure_le H).mpr hUH
    refine ⟨R, fun x ⟨v, hv⟩ => ?_⟩
    have hx : Multiplicative.ofAdd x ∉ Γ := fun hx => absurd (hΓH hx v) (not_le.mpr hv)
    exact hzero _ hx
  · -- decay
    intro N
    have hk : IsCompact (k : Set (Multiplicative (SAdeleRing F Sf))) :=
      isCompact_of_isGoodSubgroup _ k hs.2.2.1
    have hαk : IsCompact {x : Γ | π x = 1} := by
      have : {x : Γ | π x = 1} = Subtype.val ⁻¹' (k : Set (Multiplicative (SAdeleRing F Sf))) := by
        ext x; exact hπ.2.2.2.2 x
      rw [this]
      exact hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hk
    obtain ⟨A1, B1, hAB1⟩ := correspondence_growth_bound (Multiplicative (SAdeleRing F Sf)) Γ hΓo
      m n r s d hπ.1 π hπ.2.1 hπ.2.2.1 hαk _ 0 0 0 Fin.elim0
      (archCoordElem Complex.reCLM) (continuous_archCoordElem _)
    obtain ⟨A2, B2, hAB2⟩ := correspondence_growth_bound (Multiplicative (SAdeleRing F Sf)) Γ hΓo
      m n r s d hπ.1 π hπ.2.1 hπ.2.2.1 hαk _ 0 0 0 Fin.elim0
      (archCoordElem Complex.imCLM) (continuous_archCoordElem _)
    obtain ⟨C, hC⟩ := elem_decay g N
    set M : ℝ := ((Fintype.card (InfinitePlace F) : ℕ) : ℝ) with hM
    set K : ℝ := 1 + M * (|A1| + |B1| + |A2| + |B2|) with hK
    have hM0 : 0 ≤ M := Nat.cast_nonneg _
    have hK1 : 1 ≤ K := by
      have : 0 ≤ M * (|A1| + |B1| + |A2| + |B2|) := by positivity
      linarith
    refine ⟨K ^ N * max C 0, fun x => ?_⟩
    by_cases hx : Multiplicative.ofAdd x ∈ Γ
    · set p : Γ := ⟨Multiplicative.ofAdd x, hx⟩
      set S := ‖(Multiplicative.toAdd (π p)).1‖ + ‖(Multiplicative.toAdd (π p)).2.2.1‖ with hS
      have hS0 : 0 ≤ S := by positivity
      have hre : ‖archCoord (Sf := Sf) Complex.reCLM x‖ ≤ A1 * S + B1 := by
        have := hAB1 p
        have h0 : 0 ≤ ‖(Multiplicative.toAdd (archCoordElem (Sf := Sf) Complex.reCLM
          (p : Multiplicative (SAdeleRing F Sf)))).2.2.1‖ := norm_nonneg _
        exact le_trans (le_add_of_nonneg_right h0) this
      have him : ‖archCoord (Sf := Sf) Complex.imCLM x‖ ≤ A2 * S + B2 := by
        have := hAB2 p
        have h0 : 0 ≤ ‖(Multiplicative.toAdd (archCoordElem (Sf := Sf) Complex.imCLM
          (p : Multiplicative (SAdeleRing F Sf)))).2.2.1‖ := norm_nonneg _
        exact le_trans (le_add_of_nonneg_right h0) this
      have hsize : archSize x ≤ M * ((A1 * S + B1) + (A2 * S + B2)) := by
        unfold archSize
        rw [← (Fintype.equivFin (InfinitePlace F)).symm.sum_comp]
        calc ∑ j, ‖x.1 ((Fintype.equivFin (InfinitePlace F)).symm j)‖
            ≤ ∑ _j : Fin (Fintype.card (InfinitePlace F)), ((A1 * S + B1) + (A2 * S + B2)) :=
              Finset.sum_le_sum fun j _ => (norm_le_archCoord x j).trans (add_le_add hre him)
          _ = M * ((A1 * S + B1) + (A2 * S + B2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hlin : 1 + archSize x ≤ K * (1 + S) := by
        have e1 : A1 * S ≤ |A1| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
        have e2 : A2 * S ≤ |A2| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
        have e3 : B1 ≤ |B1| := le_abs_self _
        have e4 : B2 ≤ |B2| := le_abs_self _
        have e5 : (A1 * S + B1) + (A2 * S + B2) ≤ (|A1| + |B1| + |A2| + |B2|) * (1 + S) := by
          have h6 : 0 ≤ |A1| + |A2| + |B1| * S + |B2| * S := by positivity
          have h7 : (|A1| + |B1| + |A2| + |B2|) * (1 + S) =
              (|A1| * S + |B1| + (|A2| * S + |B2|)) + (|A1| + |A2| + |B1| * S + |B2| * S) := by
            ring
          rw [h7]; linarith
        have e6 := mul_le_mul_of_nonneg_left e5 hM0
        have e7 : 0 ≤ S := hS0
        calc 1 + archSize x ≤ 1 + M * ((A1 * S + B1) + (A2 * S + B2)) := by linarith
          _ ≤ 1 + M * ((|A1| + |B1| + |A2| + |B2|) * (1 + S)) := by linarith
          _ ≤ K * (1 + S) := by
            rw [hK]
            have : 0 ≤ M * (|A1| + |B1| + |A2| + |B2|) * S := by positivity
            nlinarith
      have hfx : extendPullback Γ π g.toFun (Multiplicative.ofAdd x) =
          g.toFun (Multiplicative.toAdd (π p)) := hval p
      rw [hfx]
      have hgC := hC (Multiplicative.toAdd (π p))
      have hpow : (1 + archSize x) ^ N ≤ K ^ N * (1 + S) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith [archSize_nonneg x]) hlin N
      calc ‖g.toFun (Multiplicative.toAdd (π p))‖ * (1 + archSize x) ^ N
          ≤ ‖g.toFun (Multiplicative.toAdd (π p))‖ * (K ^ N * (1 + S) ^ N) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = K ^ N * (‖g.toFun (Multiplicative.toAdd (π p))‖ * (1 + S) ^ N) := by ring
        _ ≤ K ^ N * max C 0 :=
            mul_le_mul_of_nonneg_left (hgC.trans (le_max_left _ _)) (by positivity)
    · rw [hzero _ hx, norm_zero, zero_mul]
      positivity

theorem decays_schwartz (f : SAdelicSchwartz F Sf) : Decays Sf f.toFun := by
  obtain ⟨h, hh⟩ := f
  change Decays Sf h
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact decays_extendPullback Γ k π g hs hπ
  | zero => exact decays_zero
  | add x y _ _ hx hy => exact decays_add hx hy
  | smul a x _ hx => exact decays_smul a hx

end SAdele

section Infra
open InfinitePlace.Completion

/-- Tonelli for a finite product. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (x₀ : ∀ i, X i) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  classical
  have hF : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ∀ i, X i,
      (∫⋯∫⁻_s, (fun x : ∀ i, X i => ∏ i, f i (x i)) ∂μ) x =
        (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * ∏ i ∈ sᶜ, f i (x i) := by
    intro s
    induction s using Finset.induction with
    | empty => intro x; simp
    | insert j s hj ih =>
      intro x
      rw [lmarginal_insert _ hF hj]
      have hcompl : sᶜ = insert j (insert j s)ᶜ := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [hij]
      have hjc : j ∉ (insert j s)ᶜ := by simp
      have hint : ∀ t : X j, (∫⋯∫⁻_s, (fun x : ∀ i, X i => ∏ i, f i (x i)) ∂μ)
          (Function.update x j t) =
          (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * (f j t * ∏ i ∈ (insert j s)ᶜ, f i (x i)) := by
        intro t
        rw [ih, hcompl, Finset.prod_insert hjc, Function.update_self]
        congr 2
        refine Finset.prod_congr rfl fun i hi => ?_
        have hij : i ≠ j := fun h => hjc (h ▸ hi)
        rw [Function.update_of_ne hij]
      simp_rw [hint]
      rw [lintegral_const_mul _ ((hf j).mul_const _), lintegral_mul_const _ (hf j),
        Finset.prod_insert hj]
      ring
  rw [lintegral_eq_lmarginal_univ x₀, key]
  simp

theorem isOpenEmbedding_pi_units_val {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsOpenUnits (M i)] :
    Topology.IsOpenEmbedding (fun (u : ∀ i, (M i)ˣ) (i : ι) => (u i : M i)) := by
  have h : ∀ i, Topology.IsOpenEmbedding (Units.val : (M i)ˣ → M i) :=
    fun i => IsOpenUnits.isOpenEmbedding_unitsVal
  exact ⟨Topology.IsEmbedding.piMap fun i => (h i).isEmbedding,
    (IsOpenMap.piMap (fun i => (h i).isOpenMap)
      (Filter.eventually_cofinite.mpr (Set.toFinite _))).isOpen_range⟩

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

theorem secondCountable_finite (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

noncomputable def coordEquiv : SIdeleGroup F Sf ≃*
    ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :=
  (MulEquiv.prodUnits (M := (w : InfinitePlace F) → w.Completion)
      (N := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).trans
    (MulEquiv.prodCongr MulEquiv.piUnits MulEquiv.piUnits)

theorem continuous_coordEquiv : Continuous (coordEquiv F Sf) :=
  ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).continuous.prodMap
    (ContinuousMulEquiv.piUnits
      (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous).comp
    (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous

theorem continuous_coordEquiv_symm : Continuous (coordEquiv F Sf).symm :=
  (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous.comp
    ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.continuous.prodMap
      (ContinuousMulEquiv.piUnits
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous)

noncomputable def coordVal (p : ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)) : SAdeleRing F Sf :=
  (fun w => (p.1 w : w.Completion), fun v => (p.2 v : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) := by
  have h1 : Topology.IsOpenEmbedding (coordVal F Sf) :=
    (isOpenEmbedding_pi_units_val (M := fun w : InfinitePlace F => w.Completion)).prodMap
      (isOpenEmbedding_pi_units_val
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))
  have h2 : Topology.IsOpenEmbedding (coordEquiv F Sf) :=
    (Homeomorph.mk (coordEquiv F Sf).toEquiv (continuous_coordEquiv F Sf)
      (continuous_coordEquiv_symm F Sf)).isOpenEmbedding
  exact h1.comp h2

end Infra

section Local
open InfinitePlace.Completion
variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
theorem arch_local_integrable (w : InfinitePlace F) {σ1 : ℝ} (hσ : 0 < σ1) (k : ℕ)
    (hk : (w.mult : ℝ) * σ1 < k) :
    Integrable (fun x : w.Completion => ‖x‖ ^ ((w.mult : ℝ) * σ1 - w.mult) / (max 1 ‖x‖) ^ k)
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := by
  set d := w.mult with hd
  have hRad (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
      [μ.IsAddHaarMeasure] (hdim : Module.finrank ℝ E = d) :
      Integrable (fun x : E ↦ ‖x‖ ^ ((d : ℝ) * σ1 - d) / (max 1 ‖x‖) ^ k) μ := by
    refine (integrable_fun_norm_addHaar μ (f := fun r : ℝ ↦
      r ^ ((d : ℝ) * σ1 - d) / (max 1 r) ^ k)).mpr ?_
    have hd₀ : 0 < d := InfinitePlace.mult_pos (w := w)
    have heq (r : ℝ) (hr : 0 < r) :
        r ^ (Module.finrank ℝ E - 1) • (r ^ ((d : ℝ) * σ1 - d) / (max 1 r) ^ k) =
          r ^ ((d : ℝ) * σ1 - 1) / (max 1 r) ^ k := by
      rw [smul_eq_mul, ← mul_div_assoc, hdim, ← Real.rpow_natCast, ← Real.rpow_add hr,
        Nat.cast_sub hd₀, Nat.cast_one]
      congr 2
      ring
    refine IntegrableOn.congr_fun ?_ (fun r hr ↦ (heq r hr).symm) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    apply IntegrableOn.union
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ1 - 1)) (Set.Ioc 0 1) :=
        ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by
          have hp := mul_pos (Nat.cast_pos.mpr hd₀) hσ
          linarith)).congr_set_ae Ioo_ae_eq_Ioc.symm
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioc
      simp [max_eq_left hr.2]
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ1 - 1 - k)) (Set.Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
      have hr' : 0 < r := zero_lt_one.trans hr
      rw [max_eq_right hr.le, ← Real.rpow_natCast, ← Real.rpow_sub hr']
  by_cases hw : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos hw]
    have hme : MeasurableEmbedding (ringEquivRealOfIsReal hw).symm :=
      (isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding
    rw [hme.integrable_map_iff]
    have hnorm (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ :=
      (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivRealOfIsReal hw).symm) x
    simpa only [Function.comp_def, hnorm] using hRad ℝ volume (by simp [d, hw.mult_eq_one])
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg hw]
    have hme : MeasurableEmbedding (ringEquivComplexOfIsComplex hw').symm :=
      (isometryEquivComplexOfIsComplex hw').symm.toHomeomorph.measurableEmbedding
    rw [hme.integrable_map_iff]
    have hnorm (x : ℂ) : ‖(ringEquivComplexOfIsComplex hw').symm x‖ = ‖x‖ :=
      (isometryEquivComplexOfIsComplex hw').symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivComplexOfIsComplex hw').symm) x
    have hi := hRad ℂ volume (by simp [Complex.finrank_real_complex, d, hw'.mult_eq_two])
    rw [two_nsmul]
    simpa only [Function.comp_def, hnorm] using hi.add_measure hi

omit [NumberField F] in
theorem arch_local_lintegral (w : InfinitePlace F) {σ1 : ℝ} (hσ : 0 < σ1) (k : ℕ)
    (hk : (w.mult : ℝ) * σ1 < k) :
    ∫⁻ t, ENNReal.ofReal (‖t‖ ^ ((w.mult : ℝ) * σ1) / (max 1 ‖t‖) ^ k) *
        ((‖t‖₊ : ℝ≥0∞) ^ w.mult)⁻¹
      ∂(RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_)
    (arch_local_integrable w hσ k hk).lintegral_lt_top
  have hd0 : (0 : ℝ) < w.mult := Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))
  by_cases ht : t = 0
  · subst ht
    have : (0 : ℝ) ^ ((w.mult : ℝ) * σ1) = 0 := Real.zero_rpow (by positivity)
    simp [this]
  · have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
    have h1 : ((‖t‖₊ : ℝ≥0∞) ^ w.mult)⁻¹ = ENNReal.ofReal ((‖t‖ ^ w.mult)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, enorm_eq_nnnorm]
    rw [h1, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    rw [Real.rpow_sub hpos, Real.rpow_natCast]
    field_simp

/-- The norm of a nonzero element of the completion is `q ^ log (v x)`. -/
theorem norm_eq_zpow_log (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ WithZero.log (Valued.v x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, WithZero.toAdd_unzero_eq_log]
  simp

theorem norm_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
    Valued.toNormedField.one_le_norm_iff, ← le_antisymm_iff]

theorem finite_local_mul_lintegral (v : HeightOneSpectrum (𝓞 F)) {σ1 : ℝ} (hσ : 0 < σ1)
    (R : ℝ) :
    ∫⁻ u : (v.adicCompletion F)ˣ,
        Set.indicator {t : v.adicCompletion F | t ≠ 0 ∧ ‖t‖ ≤ R}
          (fun t => ENNReal.ofReal (‖t‖ ^ σ1)) (u : v.adicCompletion F)
      ∂(finiteLocalMulTamagawa F v) < ⊤ := by
  haveI : LocallyCompactSpace (v.adicCompletion F) :=
    RiemannMasullo.locallyCompactSpace_adicCompletion v
  obtain ⟨hHaar, hunits⟩ := finiteLocalMulTamagawa_isHaarMeasure_and_units F v
  set μ := finiteLocalMulTamagawa F v with hμ
  set q : ℝ := (v.asIdeal.absNorm : ℝ) with hqdef
  have hq : 1 < q := Nat.one_lt_cast.mpr (HeightOneSpectrum.one_lt_absNorm v)
  have hq0 : 0 < q := zero_lt_one.trans hq
  obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set p : (v.adicCompletion F)ˣ := Units.mk0 π hπ0
  have hp : ‖(p : v.adicCompletion F)‖ = q⁻¹ := by
    rw [Units.val_mk0, norm_eq_zpow_log v π hπ0, hπ, WithZero.log_exp, zpow_neg_one]
  let S : ℤ → Set (v.adicCompletion F)ˣ := fun j => {u | ‖(u : v.adicCompletion F)‖ = q ^ j}
  have hS0 : μ (S 0) < ⊤ := by
    have : S 0 = {u : (v.adicCompletion F)ˣ | Valued.v (u : v.adicCompletion F) = 1} := by
      ext u
      simp only [S, zpow_zero, Set.mem_setOf_eq]
      exact norm_eq_one_iff v _
    rw [this, hunits]
    refine ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos hq0 _)))
  have hSj : ∀ j : ℤ, μ (S j) = μ (S 0) := by
    intro j
    have : S j = (fun u => p ^ j * u) ⁻¹' S 0 := by
      ext u
      simp only [S, Set.mem_preimage, Set.mem_setOf_eq, zpow_zero, Units.val_mul,
        Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hp, inv_zpow]
      rw [inv_mul_eq_one₀ (zpow_ne_zero _ hq0.ne'), eq_comm]
    rw [this, measure_preimage_mul]
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt R hq
  let T : ℕ → Set (v.adicCompletion F)ˣ := fun m => S ((N0 : ℤ) - m)
  set n : (v.adicCompletion F)ˣ → ℝ≥0∞ := fun u =>
    Set.indicator {t : v.adicCompletion F | t ≠ 0 ∧ ‖t‖ ≤ R}
      (fun t => ENNReal.ofReal (‖t‖ ^ σ1)) (u : v.adicCompletion F) with hn
  have hsupp : Function.support n ⊆ ⋃ m, T m := by
    intro u hu
    have hu' : (u : v.adicCompletion F) ∈ {t : v.adicCompletion F | t ≠ 0 ∧ ‖t‖ ≤ R} := by
      by_contra h
      exact hu (Set.indicator_of_notMem h _)
    set j := WithZero.log (Valued.v (u : v.adicCompletion F))
    have hnu : ‖(u : v.adicCompletion F)‖ = q ^ j := norm_eq_zpow_log v _ u.ne_zero
    have hj : j < N0 := by
      have h1 : q ^ j < q ^ (N0 : ℤ) := by
        rw [← hnu, zpow_natCast]; exact lt_of_le_of_lt hu'.2 hN0
      exact (zpow_lt_zpow_iff_right₀ hq).mp h1
    refine Set.mem_iUnion.mpr ⟨((N0 : ℤ) - j).toNat, ?_⟩
    have : ((N0 : ℤ) - (((N0 : ℤ) - j).toNat : ℕ)) = j := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    change ‖(u : v.adicCompletion F)‖ = q ^ ((N0 : ℤ) - (((N0 : ℤ) - j).toNat : ℕ))
    rw [this, hnu]
  have hbound : ∀ m : ℕ, ∫⁻ u in T m, n u ∂μ ≤
      ENNReal.ofReal ((q ^ ((N0 : ℤ) - m)) ^ σ1) * μ (S 0) := by
    intro m
    calc ∫⁻ u in T m, n u ∂μ ≤ ∫⁻ _ in T m, ENNReal.ofReal ((q ^ ((N0 : ℤ) - m)) ^ σ1) ∂μ := by
          refine setLIntegral_mono measurable_const fun u hu => ?_
          simp only [hn]
          refine (Set.indicator_le_self' fun _ _ => bot_le) _ |>.trans ?_
          have hu' : ‖(u : v.adicCompletion F)‖ = q ^ ((N0 : ℤ) - m) := hu
          rw [hu']
      _ = ENNReal.ofReal ((q ^ ((N0 : ℤ) - m)) ^ σ1) * μ (S 0) := by
          rw [setLIntegral_const, hSj]
  have hkey : ∀ m : ℕ, (q ^ ((N0 : ℤ) - m)) ^ σ1 = (q ^ N0) ^ σ1 * (q⁻¹ ^ σ1) ^ m := by
    intro m
    rw [zpow_sub₀ hq0.ne', zpow_natCast, zpow_natCast, div_eq_mul_inv, ← inv_pow,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (q⁻¹ ^ σ1),
      ← Real.rpow_natCast q⁻¹, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      mul_comm (m : ℝ) σ1]
  have hb1 : q⁻¹ ^ σ1 < 1 := Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hq) hσ
  have hsum : ∑' m : ℕ, ENNReal.ofReal ((q ^ ((N0 : ℤ) - m)) ^ σ1) < ⊤ := by
    simp_rw [hkey]
    simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (q ^ N0) ^ σ1),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ q⁻¹ ^ σ1)]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.mpr ?_)
    exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.mpr hb1)
  calc ∫⁻ u, n u ∂μ = ∫⁻ u in ⋃ m, T m, n u ∂μ := (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ ∑' m, ∫⁻ u in T m, n u ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal ((q ^ ((N0 : ℤ) - (m : ℤ))) ^ σ1) * μ (S 0) :=
        ENNReal.tsum_le_tsum hbound
    _ = (∑' m : ℕ, ENNReal.ofReal ((q ^ ((N0 : ℤ) - m)) ^ σ1)) * μ (S 0) := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hsum hS0

theorem finite_local_add_lintegral (v : HeightOneSpectrum (𝓞 F)) {σ1 : ℝ} (hσ : 0 < σ1)
    (R : ℝ) :
    ∫⁻ t, ENNReal.ofReal (Set.indicator {t : v.adicCompletion F | t ≠ 0 ∧ ‖t‖ ≤ R}
          (fun t => ‖t‖ ^ σ1) t) * (‖t‖₊ : ℝ≥0∞)⁻¹
      ∂(RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) < ⊤ := by
  set s0 : Set (v.adicCompletion F) := {t : v.adicCompletion F | t ≠ 0 ∧ ‖t‖ ≤ R} with hs0
  have hs0m : MeasurableSet s0 :=
    (measurableSet_singleton 0).compl.inter (measurableSet_le continuous_norm.measurable
      measurable_const)
  set n : v.adicCompletion F → ℝ≥0∞ := Set.indicator s0 (fun t => ENNReal.ofReal (‖t‖ ^ σ1))
    with hn
  have hind : ∀ t, ENNReal.ofReal (Set.indicator s0 (fun t => ‖t‖ ^ σ1) t) = n t := by
    intro t
    by_cases ht : t ∈ s0
    · simp [hn, ht]
    · simp [hn, ht]
  simp_rw [hind]
  set ν := RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
  set σv : v.adicCompletion F → ℝ≥0∞ := fun t => (‖t‖₊ : ℝ≥0∞)⁻¹ with hσv
  have hσm : Measurable σv := by simp only [hσv]; fun_prop
  have hnm : Measurable n :=
    (ENNReal.measurable_ofReal.comp (continuous_norm.rpow_const fun _ => Or.inr hσ.le).measurable).indicator hs0m
  have hval : MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).measurableEmbedding
  have hsupp : Function.support n ⊆ Set.range (Units.val : (v.adicCompletion F)ˣ → _) := by
    intro t ht
    have ht' : t ∈ s0 := by
      by_contra h
      exact ht (Set.indicator_of_notMem h _)
    exact ⟨Units.mk0 t ht'.1, rfl⟩
  set c : ℝ≥0∞ := (Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1)
    with hc
  have h1 : ∫⁻ u : (v.adicCompletion F)ˣ, n u ∂(finiteLocalMulTamagawa F v) =
      c * ∫⁻ t, n t * σv t ∂ν := by
    rw [finiteLocalMulTamagawa, lintegral_smul_measure]
    congr 1
    rw [← hval.lintegral_map n, hval.map_comap, setLIntegral_eq_of_support_subset hsupp,
      lintegral_withDensity_eq_lintegral_mul _ hσm hnm]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply]
    ring
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine (ENNReal.div_pos ?_ ?_).ne'
    · exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos.ne'
    · exact ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)
  have hfin := finite_local_mul_lintegral v hσ R
  rw [h1] at hfin
  by_contra hX
  rw [not_lt, top_le_iff] at hX
  rw [hX, ENNReal.mul_top hc0] at hfin
  exact lt_irrefl _ hfin

end Local

section Main
open InfinitePlace.Completion
variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

omit [NumberField F] in
theorem infinite_haar (w : InfinitePlace F) :
    (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

theorem coord_ne_zero_inf (g : SIdeleGroup F Sf) (w : InfinitePlace F) :
    (g : SAdeleRing F Sf).1 w ≠ 0 := by
  have : (g : SAdeleRing F Sf).1 w = ((coordEquiv F Sf g).1 w : w.Completion) := rfl
  rw [this]
  exact Units.ne_zero _

theorem coord_ne_zero_fin (g : SIdeleGroup F Sf) (v : Sf) :
    (g : SAdeleRing F Sf).2 v ≠ 0 := by
  have : (g : SAdeleRing F Sf).2 v =
      ((coordEquiv F Sf g).2 v : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) := rfl
  rw [this]
  exact Units.ne_zero _

theorem sIdeleNorm_pos (g : SIdeleGroup F Sf) : 0 < sIdeleNorm Sf g := by
  unfold sIdeleNorm
  exact mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (coord_ne_zero_inf g w)) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (coord_ne_zero_fin g v))

theorem sIdeleNorm_rpow (g : SIdeleGroup F Sf) (σ1 : ℝ) :
    sIdeleNorm Sf g ^ σ1 = (∏ w, ‖(g : SAdeleRing F Sf).1 w‖ ^ ((w.mult : ℝ) * σ1)) *
      ∏ v, ‖(g : SAdeleRing F Sf).2 v‖ ^ σ1 := by
  unfold sIdeleNorm
  rw [Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity)
      (Finset.prod_nonneg fun v _ => by positivity),
    ← Real.finset_prod_rpow Finset.univ (fun w => ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult)
      (fun w _ => by positivity),
    ← Real.finset_prod_rpow Finset.univ (fun v => ‖(g : SAdeleRing F Sf).2 v‖)
      (fun v _ => by positivity)]
  congr 1
  exact Finset.prod_congr rfl fun w _ => (Real.rpow_natCast_mul (norm_nonneg _) _ _).symm

theorem continuous_sIdeleNorm : Continuous (sIdeleNorm (F := F) Sf) := by
  have h1 : Continuous fun g : SIdeleGroup F Sf => (g : SAdeleRing F Sf) := Units.continuous_val
  have h2 : ∀ w : InfinitePlace F, Continuous fun g : SIdeleGroup F Sf =>
      (g : SAdeleRing F Sf).1 w :=
    fun w => (continuous_apply w).comp (continuous_fst.comp h1)
  have h3 : ∀ v : Sf, Continuous fun g : SIdeleGroup F Sf => (g : SAdeleRing F Sf).2 v :=
    fun v => (continuous_apply v).comp (continuous_snd.comp h1)
  exact (continuous_finsetProd _ fun w _ => ((h2 w).norm).pow _).mul
    (continuous_finsetProd _ fun v _ => (h3 v).norm)

theorem continuous_eval (f : SAdelicSchwartz F Sf) :
    Continuous fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf) :=
  (decays_schwartz f).1.comp (continuous_ofAdd.comp Units.continuous_val)

theorem integrable_norm_mul_rpow (f : SAdelicSchwartz F Sf) {σ1 : ℝ} (hσ : 0 < σ1) :
    Integrable (fun g : SIdeleGroup F Sf => ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ σ1)
      (sMultiplicativeTamagawa F Sf) := by
  classical
  obtain ⟨-, ⟨R, hR⟩, hdec⟩ := decays_schwartz f
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * σ1)
  have hkw : ∀ w : InfinitePlace F, (w.mult : ℝ) * σ1 < k := by
    intro w
    have hm : (w.mult : ℝ) ≤ 2 := by
      by_cases h : w.IsReal
      · simp [h.mult_eq_one]
      · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
    exact (mul_le_mul_of_nonneg_right hm hσ.le).trans_lt hk
  obtain ⟨B, hB⟩ := hdec (k * Fintype.card (InfinitePlace F))
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  let a : (w : InfinitePlace F) → w.Completion → ℝ :=
    fun w t => ‖t‖ ^ ((w.mult : ℝ) * σ1) / (max 1 ‖t‖) ^ k
  let b : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F → ℝ :=
    fun v t => Set.indicator {t | t ≠ 0 ∧ ‖t‖ ≤ R} (fun t => ‖t‖ ^ σ1) t
  have ha0 : ∀ w t, 0 ≤ a w t := fun w t => by positivity
  have hb0 : ∀ v t, 0 ≤ b v t := fun v t => Set.indicator_nonneg (fun _ _ => by positivity) _
  -- the pointwise bound by a product
  have hpt0 : ∀ x : SAdeleRing F Sf, (∀ v, x.2 v ≠ 0) →
      ‖f.eval x‖ * ((∏ w, ‖x.1 w‖ ^ ((w.mult : ℝ) * σ1)) * ∏ v, ‖x.2 v‖ ^ σ1) ≤
        B' * ((∏ w, a w (x.1 w)) * ∏ v, b v (x.2 v)) := by
    intro x hx2
    by_cases hsupp : ∃ v : Sf, R < ‖x.2 v‖
    · have : f.eval x = 0 := hR x hsupp
      rw [this, norm_zero, zero_mul]
      exact mul_nonneg hB'0 (mul_nonneg (Finset.prod_nonneg fun w _ => ha0 w _)
        (Finset.prod_nonneg fun v _ => hb0 v _))
    · push_neg at hsupp
      have hbv : ∀ v, b v (x.2 v) = ‖x.2 v‖ ^ σ1 := fun v =>
        Set.indicator_of_mem (show x.2 v ∈ {t | t ≠ 0 ∧ ‖t‖ ≤ R} from
          ⟨hx2 v, hsupp v⟩) _
      have hMpos : 0 < ∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k :=
        Finset.prod_pos fun w _ => pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) k
      have hprod : (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤
          (1 + archSize x) ^ (k * Fintype.card (InfinitePlace F)) := by
        calc (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k)
            ≤ ∏ _w : InfinitePlace F, (1 + archSize x) ^ k := by
              refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
              refine pow_le_pow_left₀ (by positivity) ?_ k
              refine max_le (by linarith [archSize_nonneg x]) ?_
              have : ‖x.1 w‖ ≤ archSize x :=
                Finset.single_le_sum (f := fun w : InfinitePlace F => ‖x.1 w‖)
                  (fun w _ => norm_nonneg _) (Finset.mem_univ w)
              linarith
          _ = (1 + archSize x) ^ (k * Fintype.card (InfinitePlace F)) := by
              rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      have hfB : ‖f.eval x‖ * (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤ B' := by
        refine le_trans ?_ ((hB x).trans (le_max_left _ _))
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      have hfB' : ‖f.eval x‖ ≤ B' / ∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k :=
        (le_div_iff₀ hMpos).mpr hfB
      simp_rw [hbv]
      simp only [a]
      rw [Finset.prod_div_distrib]
      have hP1 : 0 ≤ ∏ w : InfinitePlace F, ‖x.1 w‖ ^ ((w.mult : ℝ) * σ1) :=
        Finset.prod_nonneg fun w _ => by positivity
      have hP2 : 0 ≤ ∏ v : Sf, ‖x.2 v‖ ^ σ1 := Finset.prod_nonneg fun v _ => by positivity
      calc ‖f.eval x‖ * ((∏ w : InfinitePlace F, ‖x.1 w‖ ^ ((w.mult : ℝ) * σ1)) *
            ∏ v : Sf, ‖x.2 v‖ ^ σ1)
          ≤ (B' / ∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) *
              ((∏ w : InfinitePlace F, ‖x.1 w‖ ^ ((w.mult : ℝ) * σ1)) *
              ∏ v : Sf, ‖x.2 v‖ ^ σ1) := mul_le_mul_of_nonneg_right hfB' (mul_nonneg hP1 hP2)
        _ = _ := by ring
  have hpt : ∀ g : SIdeleGroup F Sf,
      ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ σ1 ≤
        B' * ((∏ w, a w ((g : SAdeleRing F Sf).1 w)) * ∏ v, b v ((g : SAdeleRing F Sf).2 v)) := by
    intro g
    rw [sIdeleNorm_rpow]
    exact hpt0 _ (coord_ne_zero_fin g)
  -- measurability
  have hmeas : AEStronglyMeasurable
      (fun g : SIdeleGroup F Sf => ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ σ1)
      (sMultiplicativeTamagawa F Sf) :=
    (((continuous_eval f).norm).mul
      (continuous_sIdeleNorm.rpow_const fun _ => Or.inr hσ.le)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  -- the lower integral
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  have hinf : ∀ w : InfinitePlace F,
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infinite_haar
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    fun v => RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hsf_inf : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) :=
    fun w => inferInstance
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F),
      SigmaFinite (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) :=
    fun v => inferInstance
  have hsc1 : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  have hb1 : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  have hbX : BorelSpace (SAdeleRing F Sf) := inferInstance
  have hembX : MeasurableEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) :=
    (isOpenEmbedding_val F Sf).measurableEmbedding
  -- densities
  set ρ : (w : InfinitePlace F) → w.Completion → ℝ≥0∞ :=
    fun w t => ((‖t‖₊ : ℝ≥0∞) ^ w.mult)⁻¹ with hρ
  set σv : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F → ℝ≥0∞ :=
    fun v t => (‖t‖₊ : ℝ≥0∞)⁻¹ with hσv
  have hρm : ∀ w, Measurable (ρ w) := fun w => by simp only [hρ]; fun_prop
  have hσm : ∀ v, Measurable (σv v) := fun v => by simp only [hσv]; fun_prop
  have hdens : (fun x : SAdeleRing F Sf =>
      ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
        ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹) =
      fun x : SAdeleRing F Sf => (∏ w, ρ w (x.1 w)) * ∏ v, σv v (x.2 v) := by
    funext x
    have h1 : (∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) ≠ ⊤ :=
      ENNReal.prod_ne_top fun w _ => ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h2 : (∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.prod_ne_top fun v _ => ENNReal.coe_ne_top
    rw [ENNReal.mul_inv (Or.inr h2) (Or.inl h1),
      ENNReal.prod_inv_distrib fun w _ w' _ _ =>
        Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      ENNReal.prod_inv_distrib fun v _ v' _ _ => Or.inr ENNReal.coe_ne_top]
  have hdensm : Measurable (fun x : SAdeleRing F Sf =>
      ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
        ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹) := by
    rw [hdens]
    exact (Finset.measurable_prod _ fun w _ => (hρm w).comp
        ((measurable_pi_apply w).comp measurable_fst)).mul
      (Finset.measurable_prod _ fun v _ => (hσm v).comp
        ((measurable_pi_apply v).comp measurable_snd))
  -- the majorant
  have ham : ∀ w, Measurable (a w) := fun w =>
    ((continuous_norm.rpow_const fun _ => Or.inr (by positivity)).div
      ((continuous_const.max continuous_norm).pow k)
      (fun t => (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) k).ne')).measurable
  have hbm : ∀ v, Measurable (b v) := fun v =>
    (continuous_norm.rpow_const fun _ => Or.inr hσ.le).measurable.indicator
      ((measurableSet_singleton 0).compl.inter
        (measurableSet_le continuous_norm.measurable measurable_const))
  let Φ : InfiniteAdeleRing F → ℝ≥0∞ := fun y => ∏ w, ENNReal.ofReal (a w (y w)) * ρ w (y w)
  let Ψ : ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) → ℝ≥0∞ :=
    fun z => ∏ v, ENNReal.ofReal (b v (z v)) * σv v (z v)
  let H : SAdeleRing F Sf → ℝ≥0∞ := fun x => ENNReal.ofReal B' *
    ((∏ w, ENNReal.ofReal (a w (x.1 w))) * ∏ v, ENNReal.ofReal (b v (x.2 v)))
  have hHm : Measurable H := by
    refine Measurable.const_mul ((Finset.measurable_prod _ fun w _ => ?_).mul
      (Finset.measurable_prod _ fun v _ => ?_)) _
    · exact ENNReal.measurable_ofReal.comp ((ham w).comp ((measurable_pi_apply w).comp measurable_fst))
    · exact ENNReal.measurable_ofReal.comp ((hbm v).comp ((measurable_pi_apply v).comp measurable_snd))
  have hΦm : Measurable Φ := Finset.measurable_prod _ fun w _ =>
    (ENNReal.measurable_ofReal.comp ((ham w).comp (measurable_pi_apply w))).mul
      ((hρm w).comp (measurable_pi_apply w))
  have hΨm : Measurable Ψ := Finset.measurable_prod _ fun v _ =>
    (ENNReal.measurable_ofReal.comp ((hbm v).comp (measurable_pi_apply v))).mul
      ((hσm v).comp (measurable_pi_apply v))
  have hle1 : ∀ g : SIdeleGroup F Sf,
      ‖‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ σ1‖ₑ ≤ H (g : SAdeleRing F Sf) := by
    intro g
    rw [← ofReal_norm, Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sIdeleNorm_pos g).le _))]
    refine (ENNReal.ofReal_le_ofReal (hpt g)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hB'0, ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ =>
        ha0 w ((g : SAdeleRing F Sf).1 w)),
      ENNReal.ofReal_prod_of_nonneg (f := fun w => a w ((g : SAdeleRing F Sf).1 w))
        (fun w _ => ha0 w _),
      ENNReal.ofReal_prod_of_nonneg (f := fun v => b v ((g : SAdeleRing F Sf).2 v))
        (fun v _ => hb0 v _)]
  have hprodH : ∀ x : SAdeleRing F Sf,
      ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
        ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹ * H x = ENNReal.ofReal B' * (Φ x.1 * Ψ x.2) := by
    intro x
    have := congrFun hdens x
    rw [this]
    simp only [H, Φ, Ψ, Finset.prod_mul_distrib]
    ring
  have hΦ : ∫⁻ y, Φ y ∂(infiniteAdditiveTamagawa F) < ⊤ := by
    have h := lintegral_pi_prod (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)
      (fun w t => ENNReal.ofReal (a w t) * ρ w t)
      (fun w => (ENNReal.measurable_ofReal.comp (ham w)).mul (hρm w)) (fun _ => 0)
    calc ∫⁻ y, Φ y ∂(infiniteAdditiveTamagawa F)
        = ∏ w, ∫⁻ t, ENNReal.ofReal (a w t) * ρ w t
            ∂(RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := h
      _ < ⊤ := ENNReal.prod_lt_top fun w _ => arch_local_lintegral w hσ k (hkw w)
  have hΨ : ∫⁻ z, Ψ z ∂(Measure.pi fun v : Sf =>
      RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) < ⊤ := by
    have h := lintegral_pi_prod (fun v : Sf =>
        RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F)))
      (fun v t => ENNReal.ofReal (b v t) * σv v t)
      (fun v => (ENNReal.measurable_ofReal.comp (hbm v)).mul (hσm v)) (fun _ => 0)
    calc ∫⁻ z, Ψ z ∂(Measure.pi fun v : Sf =>
          RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F)))
        = ∏ v : Sf, ∫⁻ t, ENNReal.ofReal (b v t) * σv v t
            ∂(RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))) := h
      _ < ⊤ := ENNReal.prod_lt_top fun v _ =>
          finite_local_add_lintegral (v : HeightOneSpectrum (𝓞 F)) hσ R
  have hS1 : SigmaFinite (infiniteAdditiveTamagawa F) :=
    inferInstanceAs
      (SigmaFinite (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)))
  calc ∫⁻ g, ‖‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ σ1‖ₑ ∂(sMultiplicativeTamagawa F Sf)
      ≤ ∫⁻ g, H (g : SAdeleRing F Sf) ∂(sMultiplicativeTamagawa F Sf) := lintegral_mono hle1
    _ = (∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))) *
        ∫⁻ x, H x ∂((sAdditiveTamagawa F Sf).withDensity
          (fun x => ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
            ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹)).restrict (Set.range Units.val) := by
        rw [sMultiplicativeTamagawa, lintegral_smul_measure, ← hembX.lintegral_map H,
          hembX.map_comap]
        rfl
    _ ≤ (∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))) *
        ∫⁻ x, H x ∂((sAdditiveTamagawa F Sf).withDensity
          (fun x => ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) *
            ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹)) := by
        gcongr
        exact Measure.restrict_le_self
    _ = (∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))) *
        (ENNReal.ofReal B' * ((∫⁻ y, Φ y ∂(infiniteAdditiveTamagawa F)) *
          ∫⁻ z, Ψ z ∂(Measure.pi fun v : Sf =>
            RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))))) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hdensm hHm]
        congr 1
        simp only [Pi.mul_apply]
        simp_rw [hprodH]
        rw [lintegral_const_mul (ENNReal.ofReal B') (f := fun x : SAdeleRing F Sf => Φ x.1 * Ψ x.2)
            ((hΦm.comp measurable_fst).mul (hΨm.comp measurable_snd)),
          sAdditiveTamagawa, lintegral_prod_mul hΦm.aemeasurable hΨm.aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.prod_lt_top fun v _ => ?_)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hΦ hΨ))
        refine lt_top_iff_ne_top.mpr ?_
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
          (by
            have h1 := HeightOneSpectrum.one_lt_absNorm v
            have : (1 : ℝ≥0∞) < (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by exact_mod_cast h1
            exact (tsub_pos_of_lt this).ne')

end Main

/-- `r ^ x |log r| ≤ 4/σ (r ^ (σ/4) + r ^ (7σ/4))` for `x ∈ (σ/2, 3σ/2)` and `r > 0`. -/
theorem rpow_mul_abs_log_le_of_mem_Ioo {σ x r : ℝ} (hσ : 0 < σ)
    (hx : x ∈ Set.Ioo (σ / 2) (3 * σ / 2)) (hr : 0 < r) :
    r ^ x * |Real.log r| ≤ 4 / σ * (r ^ (σ / 4) + r ^ (7 * σ / 4)) := by
  have hε : 0 < σ / 4 := by positivity
  rcases le_or_gt 1 r with h1 | h1
  · have hlog := Real.log_le_rpow_div hr.le hε
    have hpow : r ^ x ≤ r ^ (3 * σ / 2) := Real.rpow_le_rpow_of_exponent_le h1 hx.2.le
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    calc r ^ x * Real.log r ≤ r ^ (3 * σ / 2) * (r ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg h1) (by positivity)
      _ = 4 / σ * r ^ (7 * σ / 4) := by
          rw [mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]
  · have hlog := Real.log_le_rpow_div (inv_pos.mpr hr).le hε
    have hpow : r ^ x ≤ r ^ (σ / 2) := Real.rpow_le_rpow_of_exponent_ge hr h1.le hx.1.le
    rw [abs_of_neg (Real.log_neg hr h1), ← Real.log_inv]
    calc r ^ x * Real.log r⁻¹ ≤ r ^ (σ / 2) * (r⁻¹ ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg ((one_le_inv₀ hr).mpr h1.le)) (by positivity)
      _ = 4 / σ * r ^ (σ / 4) := by
          rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (7 * σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]

end Sol_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn

open MasulloGRH Sol_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn Topology in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (f : SAdelicSchwartz F Sf) (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) :
    (∀ s : ℂ, 0 < σ + s.re →
      Integrable (fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c s g)
        (sMultiplicativeTamagawa F Sf)) ∧
    DifferentiableOn ℂ (fun s : ℂ => sZetaIntegral f (sQuasiTwist Sf c s))
      {s : ℂ | 0 < σ + s.re} := by
  have hr : ∀ g : SIdeleGroup F Sf, 0 < sIdeleNorm Sf g := sIdeleNorm_pos
  have hcont_r : Continuous fun g : SIdeleGroup F Sf => ((sIdeleNorm Sf g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_sIdeleNorm
  have hnormF : ∀ (z : ℂ) (g : SIdeleGroup F Sf),
      ‖f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c z g‖ =
        ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ (σ + z.re) := by
    intro z g
    simp only [sQuasiTwist]
    rw [norm_mul, norm_mul, hσ g, Complex.norm_cpow_eq_rpow_re_of_pos (hr g),
      Real.rpow_add (hr g)]
  have hcontF : ∀ z : ℂ, Continuous fun g : SIdeleGroup F Sf =>
      f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c z g := by
    intro z
    exact (continuous_eval f).mul (hc.1.mul (hcont_r.cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.mpr (hr g)))
  have hint : ∀ z : ℂ, 0 < σ + z.re → Integrable (fun g : SIdeleGroup F Sf =>
      f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c z g) (sMultiplicativeTamagawa F Sf) :=
    fun z hz => (integrable_norm_mul_rpow f hz).mono' (hcontF z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => le_of_eq (hnormF z g))
  refine ⟨hint, ?_⟩
  intro s0 hs0
  have hσ0 : 0 < σ + s0.re := hs0
  set σ0 := σ + s0.re with hσ0def
  let V : Set ℂ := {z : ℂ | σ + z.re ∈ Set.Ioo (σ0 / 2) (3 * σ0 / 2)}
  have hV : V ∈ 𝓝 s0 := by
    have : IsOpen V := isOpen_Ioo.preimage (continuous_const.add Complex.continuous_re)
    exact this.mem_nhds
      (show σ + s0.re ∈ Set.Ioo (σ0 / 2) (3 * σ0 / 2) from ⟨by linarith, by linarith⟩)
  let W : ℂ → SIdeleGroup F Sf → ℂ :=
    fun z g => f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c z g
  let D : ℂ → SIdeleGroup F Sf → ℂ :=
    fun z g => W z g * Complex.log ((sIdeleNorm Sf g : ℝ) : ℂ)
  have hmeas : ∀ᶠ z in 𝓝 s0, AEStronglyMeasurable (W z) (sMultiplicativeTamagawa F Sf) :=
    Filter.Eventually.of_forall fun z => (hcontF z).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D s0) (sMultiplicativeTamagawa F Sf) :=
    (hcontF s0).aestronglyMeasurable.mul
      (Complex.measurable_log.comp hcont_r.measurable).aestronglyMeasurable
  let bound : SIdeleGroup F Sf → ℝ := fun g => 4 / σ0 *
    (‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ (σ0 / 4) +
      ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ (7 * σ0 / 4))
  have hbound : Integrable bound (sMultiplicativeTamagawa F Sf) :=
    ((integrable_norm_mul_rpow f (by positivity)).add
      (integrable_norm_mul_rpow f (by positivity))).const_mul _
  have hDbound : ∀ᵐ g ∂(sMultiplicativeTamagawa F Sf), ∀ z ∈ V, ‖D z g‖ ≤ bound g :=
    Filter.Eventually.of_forall fun g z hz => by
      have hlog : Complex.log ((sIdeleNorm Sf g : ℝ) : ℂ) =
          ((Real.log (sIdeleNorm Sf g) : ℝ) : ℂ) :=
        (Complex.ofReal_log (hr g).le).symm
      simp only [D, W]
      rw [norm_mul, hnormF, hlog, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      calc ‖f.eval (g : SAdeleRing F Sf)‖ *
            (sIdeleNorm Sf g ^ (σ + z.re) * |Real.log (sIdeleNorm Sf g)|)
          ≤ ‖f.eval (g : SAdeleRing F Sf)‖ *
            (4 / σ0 * (sIdeleNorm Sf g ^ (σ0 / 4) + sIdeleNorm Sf g ^ (7 * σ0 / 4))) :=
            mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le_of_mem_Ioo hσ0 hz (hr g))
              (norm_nonneg _)
        _ = bound g := by simp only [bound]; ring
  have hdiff : ∀ᵐ g ∂(sMultiplicativeTamagawa F Sf), ∀ z ∈ V,
      HasDerivAt (fun w => W w g) (D z g) z :=
    Filter.Eventually.of_forall fun g z _ => by
      have hg : ((sIdeleNorm Sf g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr g).ne'
      simp only [W, D, sQuasiTwist]
      simpa only [id_eq, mul_assoc, mul_one] using
        (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul (c g)).const_mul
          (f.eval (g : SAdeleRing F Sf))
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas (hint s0 hs0) hDmeas
    hDbound hbound hdiff).2
  exact key.differentiableAt.differentiableWithinAt
