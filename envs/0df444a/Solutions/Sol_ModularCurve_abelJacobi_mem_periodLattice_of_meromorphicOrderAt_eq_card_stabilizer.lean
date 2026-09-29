-- Prove2me | solution 1 for ModularCurve.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2074f7c3-14b5-5978-8416-277587202dda

import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSum
import Theorems.Thm_ModularCurve_eventually_abelFibreSum_sub_mem_periodLattice
import Theorems.Thm_ModularCurve_periodAlong_smul_sub_periodAlong_eq_period
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one"

open UpperHalfPlane Filter Topology
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "valueMultiplicity orbifoldIndex abelFibreSum periodAlong period periodLattice period_mem_periodLattice eventually_abelFibreSum_sub_mem_periodLattice periodAlong_smul_sub_periodAlong_eq_period"
namespace AbelNecessity
p2m_open "ModularCurve"

section Order

variable {f : ℂ → ℂ} {x : ℂ}

theorem order_inv_sub_inv_eq (hf : MeromorphicAt f x) {t : ℂ} (ht : t ≠ 0) {n : ℤ} (hn : 0 < n)
    (h : meromorphicOrderAt (fun z => f z - t) x = n) :
    meromorphicOrderAt (fun z => (f z)⁻¹ - t⁻¹) x = n := by
  have hsub : MeromorphicAt (fun z => f z - t) x := hf.sub (MeromorphicAt.const t x)
  have hpos : 0 < meromorphicOrderAt (fun z => f z - t) x := by
    rw [h]; exact_mod_cast hn
  have h0 : Tendsto (fun z => f z - t) (𝓝[≠] x) (𝓝 0) := tendsto_zero_of_meromorphicOrderAt_pos hpos
  have hft : Tendsto f (𝓝[≠] x) (𝓝 t) := by
    have := h0.add_const t
    simpa using this
  have hne : ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 := hft.eventually_ne ht

  set u : ℂ → ℂ := fun z => -t⁻¹ * (f z)⁻¹ with hu
  have hu_mero : MeromorphicAt u x := (MeromorphicAt.const _ x).mul hf.inv
  have hu_lim : Tendsto u (𝓝[≠] x) (𝓝 (-t⁻¹ * t⁻¹)) :=
    (hft.inv₀ ht).const_mul _
  have hu_ord : meromorphicOrderAt u x = 0 := by
    refine (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hu_mero).1 ⟨_, ?_, hu_lim⟩
    simp [ht]
  have hcongr : (fun z => (f z)⁻¹ - t⁻¹) =ᶠ[𝓝[≠] x] ((fun z => f z - t) * u) := by
    filter_upwards [hne] with z hz
    simp only [hu, Pi.mul_apply]
    field_simp
    ring
  rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_mul hsub hu_mero, h, hu_ord, add_zero]

noncomputable def mult (f : ℂ → ℂ) (t : ℂ) (x : ℂ) : ℕ :=
  (meromorphicOrderAt (fun z => f z - t) x).untop₀.toNat

theorem exists_of_mult_ne_zero {f : ℂ → ℂ} {t : ℂ} {x : ℂ} (h : mult f t x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ meromorphicOrderAt (fun z => f z - t) x = ((n : ℤ) : WithTop ℤ) := by
  unfold mult at h
  cases ho : meromorphicOrderAt (fun z => f z - t) x with
  | top => simp [ho] at h
  | coe a =>
    rw [ho] at h
    simp only [WithTop.untop₀_coe] at h
    refine ⟨a.toNat, Nat.pos_of_ne_zero h, ?_⟩
    have ha : 0 ≤ a := by
      by_contra hlt
      push Not at hlt
      exact h (Int.toNat_eq_zero.mpr hlt.le)
    rw [Int.toNat_of_nonneg ha]

theorem mult_of_eq_coe {f : ℂ → ℂ} {t : ℂ} {x : ℂ} {n : ℕ}
    (h : meromorphicOrderAt (fun z => f z - t) x = ((n : ℤ) : WithTop ℤ)) : mult f t x = n := by
  simp [mult, h]

theorem mult_inv_of_ne_zero (hf : MeromorphicAt f x) {t : ℂ} (ht : t ≠ 0) (h : mult f t x ≠ 0) :
    mult (fun z => (f z)⁻¹) t⁻¹ x = mult f t x := by
  obtain ⟨n, hn, hord⟩ := exists_of_mult_ne_zero h
  have := order_inv_sub_inv_eq hf ht (by exact_mod_cast hn) hord
  rw [mult_of_eq_coe hord, mult_of_eq_coe this]

theorem mult_inv (hf : MeromorphicAt f x) {t : ℂ} (ht : t ≠ 0) :
    mult (fun z => (f z)⁻¹) t⁻¹ x = mult f t x := by
  by_cases h : mult f t x ≠ 0
  · exact mult_inv_of_ne_zero hf ht h
  push Not at h
  by_cases h' : mult (fun z => (f z)⁻¹) t⁻¹ x ≠ 0
  · have key : mult (fun z => ((fun z => (f z)⁻¹) z)⁻¹) t⁻¹⁻¹ x = mult (fun z => (f z)⁻¹) t⁻¹ x :=
      mult_inv_of_ne_zero (f := fun z => (f z)⁻¹) hf.inv (inv_ne_zero ht) h'
    simp only [inv_inv] at key
    exact key.symm
  push Not at h'
  rw [h, h']

end Order

section Stabilizer

variable {N : ℕ}

theorem finite_setOf_smul_eq (τ : ℍ) : {g : SL(2, ℤ) | g • τ = τ}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_stabilizer' (↥𝒮ℒ) τ
  let φ : SL(2, ℤ) → ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using this
  have hset : {g : SL(2, ℤ) | g • τ = τ} = φ ⁻¹' {s : ↥𝒮ℒ | s • τ = τ} := by
    ext g
    rfl
  rw [hset]
  exact h.preimage hφ.injOn

scoped instance finite_stabilizer (τ : ℍ) :
    Finite (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  have h := finite_setOf_smul_eq τ
  have : Set.Finite ((MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :
      Set (CongruenceSubgroup.Gamma0 N))) := by
    have hsub : (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :
        Set (CongruenceSubgroup.Gamma0 N)) = Subtype.val ⁻¹' {g : SL(2, ℤ) | g • τ = τ} := by
      ext γ
      simp [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub]
    exact h.preimage Subtype.val_injective.injOn
  exact this.to_subtype

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem]

theorem two_le_card_stabilizer (τ : ℍ) :
    2 ≤ Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  have hnt : Nontrivial (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
    have h1 : (⟨-1, neg_one_mem_Gamma0⟩ : CongruenceSubgroup.Gamma0 N) ∈
        MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ := by
      rw [MulAction.mem_stabilizer_iff]
      show (-1 : SL(2, ℤ)) • τ = τ
      simp
    refine ⟨⟨1, ⟨_, h1⟩, ?_⟩⟩
    intro h
    have h' := congrArg (fun x : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ =>
      (((x : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simp at h'
  exact Finite.one_lt_card_iff_nontrivial.mpr hnt

theorem orbifoldIndex_pos (N : ℕ) (τ : ℍ) : 0 < ModularCurve.orbifoldIndex N τ :=
  Nat.div_pos (two_le_card_stabilizer τ) two_pos

end Stabilizer

section Shift

variable (N : ℕ) [NeZero N]

local notation "πq" => Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)

theorem periodAlong_smul_sub_mem (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ModularCurve.periodAlong N UpperHalfPlane.I (γ • τ) -
      ModularCurve.periodAlong N UpperHalfPlane.I τ ∈ ModularCurve.periodLattice N := by
  have h := ModularCurve.periodAlong_smul_sub_periodAlong_eq_period N γ τ
  have h' : ModularCurve.periodAlong N UpperHalfPlane.I (γ • τ) -
      ModularCurve.periodAlong N UpperHalfPlane.I τ = ModularCurve.period N γ := h
  rw [h']
  exact ModularCurve.period_mem_periodLattice N γ

theorem periodAlong_out_sub_mem (τ : ℍ) :
    ModularCurve.periodAlong N UpperHalfPlane.I ((πq τ).out) -
      ModularCurve.periodAlong N UpperHalfPlane.I τ ∈ ModularCurve.periodLattice N := by
  obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) τ
  rw [← hγ]
  exact periodAlong_smul_sub_mem N γ τ

theorem sum_mapDomain_sub_sum_mem (c : ℍ →₀ ℤ) :
    ((Finsupp.mapDomain πq c).sum fun ξ n => n • ModularCurve.periodAlong N UpperHalfPlane.I ξ.out) -
      (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
        ModularCurve.periodLattice N := by
  rw [Finsupp.sum_mapDomain_index
    (h := fun ξ n => n • ModularCurve.periodAlong N UpperHalfPlane.I (Quotient.out ξ))
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [← smul_sub]
  exact Submodule.smul_mem _ _ (periodAlong_out_sub_mem N τ)

end Shift

section Global

variable {N : ℕ} [NeZero N]

scoped instance countable_SL2Z : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by unfold Matrix; infer_instance
  exact Subtype.countable

def cuspValues (F : ℍ → ℂ) : Set ℂ :=
  {t | ∃ σ : SL(2, ℤ), Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 t)}

theorem countable_cuspValues (F : ℍ → ℂ) : (cuspValues F).Countable := by
  have : cuspValues F =
      ⋃ σ : SL(2, ℤ), {t | Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 t)} := by
    ext t; simp [cuspValues]
  rw [this]
  refine Set.countable_iUnion fun σ => Set.Subsingleton.countable ?_
  intro t ht s hs
  exact tendsto_nhds_unique ht hs

theorem not_mem_cuspValues_of_ne {F : ℍ → ℂ} {t : ℂ}
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    t ∉ cuspValues F := by
  rintro ⟨σ, hσ⟩
  obtain ⟨L, hL, hL'⟩ := hcusp σ
  exact hL (tendsto_nhds_unique hL' hσ)

theorem abelFibreSum_sub_mem_of_not_mem_cuspValues (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {t t' : ℂ} (ht : t ∉ cuspValues F) (ht' : t' ∉ cuspValues F) :
    ModularCurve.abelFibreSum N F t - ModularCurve.abelFibreSum N F t' ∈
      ModularCurve.periodLattice N := by
  have hW : IsPreconnected (cuspValues F)ᶜ :=
    ((countable_cuspValues F).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  set Λ := ModularCurve.periodLattice N with hΛ
  let g : ↥((cuspValues F)ᶜ) →
      (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ⧸ Λ :=
    fun s => Submodule.Quotient.mk (ModularCurve.abelFibreSum N F s)
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have hs : (s : ℂ) ∉ cuspValues F := s.2
    have hcusp' : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ (s : ℂ) ∧
        Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L) := by
      intro σ
      obtain ⟨L, hL⟩ := hcusp σ
      refine ⟨L, ?_, hL⟩
      rintro rfl
      exact hs ⟨σ, hL⟩
    have hLC := ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice F hF hΓ hnc (s : ℂ)
      hcusp'
    have hpull : ∀ᶠ y : ↥((cuspValues F)ᶜ) in 𝓝 s, ModularCurve.abelFibreSum N F (y : ℂ) -
        ModularCurve.abelFibreSum N F (s : ℂ) ∈ Λ :=
      (continuous_subtype_val.continuousAt.tendsto).eventually hLC
    filter_upwards [hpull] with y hy
    exact (Submodule.Quotient.eq Λ).2 hy
  haveI : PreconnectedSpace ↥((cuspValues F)ᶜ) := Subtype.preconnectedSpace hW
  have key := hg.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨t', ht'⟩
  exact (Submodule.Quotient.eq Λ).1 key

end Global

section Degenerate

variable {N : ℕ}

local notation "πq" => Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)

theorem mapDomain_eq_zero_of_order_eq_top (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (cq : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) →₀ ℤ)
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndex N τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ))
    {t : ℂ} {τ₀ : ℍ}
    (hdeg : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ₀ : ℂ) = ⊤) : cq = 0 := by

  have ht : t ≠ 0 := by
    rintro rfl
    have := hord τ₀
    simp only [sub_zero] at hdeg
    rw [hdeg] at this
    exact WithTop.top_ne_coe this

  have hall : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤ := by
    intro τ
    by_contra hne
    have hmero : MeromorphicOn (fun z : ℂ => F (ofComplex z) - t) {z : ℂ | 0 < z.im} := by
      intro z hz
      have := (hF ⟨z, hz⟩).sub (MeromorphicAt.const t _)
      exact this
    have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected hpre τ.im_pos τ₀.im_pos hne) hdeg

  have hzero : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = 0 := by
    intro τ
    have hev := meromorphicOrderAt_eq_top_iff.1 (hall τ)
    have hcongr : (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => t := by
      filter_upwards [hev] with z hz
      exact sub_eq_zero.1 hz
    rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_const]
    simp [ht]
  ext ξ
  have h := hord ξ.out
  rw [hzero, Quotient.out_eq] at h
  have h' : ((ModularCurve.orbifoldIndex N ξ.out : ℤ) * cq ξ : ℤ) = 0 := by
    exact_mod_cast h.symm
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact absurd (by exact_mod_cast h1) (orbifoldIndex_pos N ξ.out).ne'
  · simpa using h1

end Degenerate

section Compare

variable {N : ℕ}

local notation "πq" => Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)
local notation "Xq" => Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)

theorem valueMultiplicity_eq_mult (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) :
    ModularCurve.valueMultiplicity F t τ = mult (fun z : ℂ => F (ofComplex z)) t (τ : ℂ) := rfl

theorem abelFibreSum_inv (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) {t : ℂ} (ht : t ≠ 0) :
    ModularCurve.abelFibreSum N (fun τ => (F τ)⁻¹) t⁻¹ = ModularCurve.abelFibreSum N F t := by
  unfold ModularCurve.abelFibreSum
  refine finsum_congr fun ξ => ?_
  have : ModularCurve.valueMultiplicity (fun τ => (F τ)⁻¹) t⁻¹ ξ.out =
      ModularCurve.valueMultiplicity F t ξ.out := by
    rw [valueMultiplicity_eq_mult, valueMultiplicity_eq_mult]
    exact mult_inv (hF _) ht
  rw [this]

theorem abelFibreSum_zero_sub_abelFibreSum_inv_zero (F : ℍ → ℂ)
    (cq : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) →₀ ℤ)
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndex N τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ)) :
    ModularCurve.abelFibreSum N F 0 - ModularCurve.abelFibreSum N (fun τ => (F τ)⁻¹) 0 =
      cq.sum fun ξ n => n • ModularCurve.periodAlong N UpperHalfPlane.I ξ.out := by
  classical
  set e : Xq → ℕ := fun ξ => ModularCurve.orbifoldIndex N ξ.out with he
  set k : Xq → ℤ := fun ξ => (e ξ : ℤ) * cq ξ with hk
  set P : Xq → Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    fun ξ => ModularCurve.periodAlong N UpperHalfPlane.I ξ.out with hP
  have he_pos : ∀ ξ, 0 < e ξ := fun ξ => orbifoldIndex_pos N ξ.out

  have hvF : ∀ ξ : Xq, ModularCurve.valueMultiplicity F 0 ξ.out = (k ξ).toNat := by
    intro ξ
    unfold ModularCurve.valueMultiplicity
    simp only [sub_zero]
    rw [hord ξ.out, Quotient.out_eq, WithTop.untop₀_coe]
  have hvG : ∀ ξ : Xq, ModularCurve.valueMultiplicity (fun τ => (F τ)⁻¹) 0 ξ.out = (-k ξ).toNat := by
    intro ξ
    unfold ModularCurve.valueMultiplicity
    simp only [sub_zero]
    rw [show (fun z : ℂ => (F (ofComplex z))⁻¹) = (fun z : ℂ => F (ofComplex z))⁻¹ from rfl,
      meromorphicOrderAt_inv, hord ξ.out, Quotient.out_eq, WithTop.untop₀_neg, WithTop.untop₀_coe]

  set sF : Xq → Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    fun ξ => ((ModularCurve.valueMultiplicity F 0 ξ.out : ℂ) /
      (ModularCurve.orbifoldIndex N ξ.out : ℂ)) • P ξ with hsF
  set sG : Xq → Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    fun ξ => ((ModularCurve.valueMultiplicity (fun τ => (F τ)⁻¹) 0 ξ.out : ℂ) /
      (ModularCurve.orbifoldIndex N ξ.out : ℂ)) • P ξ with hsG
  have hdiff : ∀ ξ, sF ξ - sG ξ = ((cq ξ : ℤ) : ℂ) • P ξ := by
    intro ξ
    simp only [hsF, hsG, hvF, hvG]
    rw [← sub_smul, ← sub_div]
    congr 1
    have h1 : ((k ξ).toNat : ℂ) - ((-k ξ).toNat : ℂ) = (k ξ : ℂ) := by
      have := Int.toNat_sub_toNat_neg (k ξ)
      exact_mod_cast this
    rw [h1]
    have hne : (ModularCurve.orbifoldIndex N ξ.out : ℂ) ≠ 0 := by
      exact_mod_cast (he_pos ξ).ne'
    simp only [hk, he]
    push_cast
    rw [mul_div_cancel_left₀ _ hne]
  have hsuppF : Function.support sF ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp only [hsF, hvF, hk, hc, mul_zero, Int.toNat_zero, Nat.cast_zero, zero_div, zero_smul]
  have hsuppG : Function.support sG ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp only [hsG, hvG, hk, hc, mul_zero, neg_zero, Int.toNat_zero, Nat.cast_zero, zero_div,
      zero_smul]
  have hfinF : (Function.support sF).Finite := cq.support.finite_toSet.subset hsuppF
  have hfinG : (Function.support sG).Finite := cq.support.finite_toSet.subset hsuppG
  have hLHS : ModularCurve.abelFibreSum N F 0 - ModularCurve.abelFibreSum N (fun τ => (F τ)⁻¹) 0 =
      ∑ᶠ ξ, (sF ξ - sG ξ) := by
    rw [finsum_sub_distrib hfinF hfinG]
    rfl
  rw [hLHS, finsum_congr hdiff]
  have hsupp : Function.support (fun ξ : Xq => ((cq ξ : ℤ) : ℂ) • P ξ) ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp [hc]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finsupp.sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  exact Int.cast_smul_eq_zsmul ℂ (cq ξ) (P ξ)

end Compare

section Main

variable {N : ℕ} [NeZero N]

local notation "πq" => Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)

theorem abel_necessity (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 : ℕ) *
        Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)) c
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) τ) : ℤ) :
        WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N := by
  set Λ := ModularCurve.periodLattice N with hΛ
  set cq := Finsupp.mapDomain πq c with hcq
  have hord' : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndex N τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ) := hord

  suffices key : (cq.sum fun ξ n => n • ModularCurve.periodAlong N UpperHalfPlane.I ξ.out) ∈ Λ by
    have hshift := sum_mapDomain_sub_sum_mem N c
    have := Λ.sub_mem key hshift
    simpa [hcq] using this
  by_cases hdeg : ∃ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤
  ·
    obtain ⟨t, τ₀, hdeg⟩ := hdeg
    have : cq = 0 := mapDomain_eq_zero_of_order_eq_top F hF cq hord' hdeg
    simp [this]
  push Not at hdeg

  set G : ℍ → ℂ := fun τ => (F τ)⁻¹ with hG
  have hGmero : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => G (ofComplex z)) (τ : ℂ) :=
    fun τ => (hF τ).inv
  have hGΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, G (γ • τ) = G τ := by
    intro γ hγ τ
    simp only [hG, hΓ γ hγ τ]
  have hncG : ∀ (s : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => G (ofComplex z) - s) (τ : ℂ) ≠ ⊤ := by
    intro s τ h
    have hev := meromorphicOrderAt_eq_top_iff.1 h
    apply hdeg s⁻¹ τ
    apply meromorphicOrderAt_eq_top_iff.2
    filter_upwards [hev] with z hz
    have hz' : (F (ofComplex z))⁻¹ = s := sub_eq_zero.1 hz
    rw [sub_eq_zero, ← inv_inv (F (ofComplex z)), hz']
  have hcuspF : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L) :=
    fun σ => (hcusp σ).imp fun _ h => h.2
  have hcuspG' : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => G (σ • τ)) atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hL0, hL⟩ := hcusp σ
    exact ⟨L⁻¹, inv_ne_zero hL0, hL.inv₀ hL0⟩
  have hcuspG : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => G (σ • τ)) atImInfty (𝓝 L) :=
    fun σ => (hcuspG' σ).imp fun _ h => h.2
  have h0F : (0 : ℂ) ∉ cuspValues F := not_mem_cuspValues_of_ne hcusp
  have h0G : (0 : ℂ) ∉ cuspValues G := not_mem_cuspValues_of_ne hcuspG'

  obtain ⟨t, ht⟩ : (cuspValues F ∪ {0} ∪ Inv.inv '' cuspValues G)ᶜ.Nonempty := by
    have hcount : (cuspValues F ∪ {0} ∪ Inv.inv '' cuspValues G).Countable :=
      ((countable_cuspValues F).union (Set.countable_singleton 0)).union
        ((countable_cuspValues G).image _)
    exact (hcount.dense_compl ℝ).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or,
    not_exists, not_and] at ht
  obtain ⟨⟨htF, ht0⟩, htG⟩ := ht
  have htG' : t⁻¹ ∉ cuspValues G := fun h => htG t⁻¹ h (inv_inv t)

  have h1 : ModularCurve.abelFibreSum N F 0 - ModularCurve.abelFibreSum N F t ∈ Λ :=
    abelFibreSum_sub_mem_of_not_mem_cuspValues F hF hΓ hdeg hcuspF h0F htF
  have h2 : ModularCurve.abelFibreSum N G t⁻¹ - ModularCurve.abelFibreSum N G 0 ∈ Λ :=
    abelFibreSum_sub_mem_of_not_mem_cuspValues G hGmero hGΓ hncG hcuspG htG' h0G
  have h3 : ModularCurve.abelFibreSum N G t⁻¹ = ModularCurve.abelFibreSum N F t :=
    abelFibreSum_inv F hF ht0
  have h4 : ModularCurve.abelFibreSum N F 0 - ModularCurve.abelFibreSum N G 0 ∈ Λ := by
    have := Λ.add_mem h1 h2
    rw [h3] at this
    convert this using 1
    abel
  rwa [abelFibreSum_zero_sub_abelFibreSum_inv_zero F cq hord'] at h4

end Main

end ModularCurve.AbelNecessity
p2m_reactivate "P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve.AbelNecessity"
p2m_reactivate "P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve"

theorem solution
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 : ℕ) *
        Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)) c
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) τ) : ℤ) :
        WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N :=
  ModularCurve.AbelNecessity.abel_necessity c F hF hΓ hcusp hord

end S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
end P2MW
export P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer (solution)
