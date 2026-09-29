-- Prove2me | solution 1 for Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/df53355e-ac3a-5d87-95e4-36768660cca7

import Mathlib
import Theorems.Thm_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff

set_option autoImplicit false

universe u

open TensorProduct

namespace SeesawPin29

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝔪" => IsLocalRing.maximalIdeal R

section Core

variable {E : Type*} [AddCommGroup E] [Module R E]

omit [IsLocalRing R] in
theorem factor_mk {p p' : Ideal R} (h : p ≤ p') (x : R) :
    Submodule.factor h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem smul_eq_zero_of_mem {r : R} (hr : r ∈ 𝔪) (ψ : E →ₗ[R] R ⧸ 𝔪) : r • ψ = 0 := by
  ext x
  rw [LinearMap.smul_apply, LinearMap.zero_apply]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective 𝔪 (ψ x)
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ hr

theorem isUnit_of_mk_ne_zero {c : R} (hc : (Submodule.Quotient.mk c : R ⧸ 𝔪) ≠ 0) : IsUnit c := by
  by_contra h
  exact hc ((Submodule.Quotient.mk_eq_zero 𝔪).mpr ((IsLocalRing.mem_maximalIdeal c).mpr h))

theorem span_singleton_eq_top [Module.Finite R E] (ψ₀ : E →ₗ[R] R ⧸ 𝔪)
    (hU : ∀ ψ : E →ₗ[R] R ⧸ 𝔪, ∃ r : R, ψ = r • ψ₀) (e : E) (he : ψ₀ e ≠ 0) :
    Submodule.span R {e} = ⊤ := by
  classical
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪

  set N : Submodule R E := Submodule.span R {e} ⊔ 𝔪 • ⊤ with hN
  suffices hN' : N = ⊤ by
    have := Submodule.le_of_le_smul_of_le_jacobson_bot (N := Submodule.span R {e}) (N' := ⊤)
      (Module.Finite.fg_top (R := R) (M := E)) (IsLocalRing.maximalIdeal_le_jacobson ⊥) (by rw [← hN, hN'])
    exact top_le_iff.mp this
  by_contra hne

  have htors : Module.IsTorsionBySet R (E ⧸ N) 𝔪 := by
    rintro q ⟨r, hr⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr Submodule.mem_top)
  letI : Module (R ⧸ 𝔪) (E ⧸ N) := htors.module
  haveI : IsScalarTower R (R ⧸ 𝔪) (E ⧸ N) := htors.isScalarTower
  have hq : ∃ q : E ⧸ N, q ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_top_iff]
    intro x _
    rw [← Submodule.Quotient.mk_eq_zero]; exact h _
  obtain ⟨q, hq⟩ := hq
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (R ⧸ 𝔪) (E ⧸ N), f q ≠ 0 := by
    by_contra h; push Not at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff (R ⧸ 𝔪) q).mp h)
  let ψ : E →ₗ[R] R ⧸ 𝔪 := (f.restrictScalars R) ∘ₗ N.mkQ
  obtain ⟨r, hr⟩ := hU ψ
  have hψe : ψ e = 0 := by
    show f (Submodule.Quotient.mk e) = 0
    have : (Submodule.Quotient.mk e : E ⧸ N) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, hN]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self e)
    rw [this, map_zero]

  have hrm : r ∈ 𝔪 := by
    by_contra hru
    have hu : IsUnit r := by
      by_contra h; exact hru ((IsLocalRing.mem_maximalIdeal r).mpr h)
    have h1 : r • ψ₀ e = 0 := by rw [← LinearMap.smul_apply, ← hr]; exact hψe
    apply he
    have := congrArg (fun z => ((hu.unit⁻¹ : Rˣ) : R) • z) h1
    simpa [smul_smul, IsUnit.val_inv_mul] using this
  have hψ0 : ψ = 0 := by rw [hr]; exact smul_eq_zero_of_mem hrm ψ₀
  apply hf
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
  exact LinearMap.congr_fun hψ0 x

variable [IsNoetherianRing R]

theorem core [Module.Finite R E] (I : Ideal R) (hI : I ≤ 𝔪) (hIN : ∃ N : ℕ, 𝔪 ^ N ≤ I)
    (ψ₀ : E →ₗ[R] R ⧸ 𝔪) (hψ₀ : ψ₀ ≠ 0) (hU : ∀ ψ : E →ₗ[R] R ⧸ 𝔪, ∃ r : R, ψ = r • ψ₀)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ 𝔪), (∃ N : ℕ, 𝔪 ^ N ≤ J') →
      ((∀ ψ : E →ₗ[R] R ⧸ 𝔪, ∃ φ : E →ₗ[R] R ⧸ J', (Submodule.factor hJ') ∘ₗ φ = ψ) ↔ I ≤ J')) :
    Nonempty (E ≃ₗ[R] R ⧸ I) := by
  classical

  obtain ⟨e, he⟩ : ∃ e : E, ψ₀ e ≠ 0 := by
    by_contra h; push Not at h; exact hψ₀ (LinearMap.ext fun x => by rw [h]; rfl)
  have hspan := span_singleton_eq_top ψ₀ hU e he

  let g : R →ₗ[R] E := LinearMap.toSpanSingleton R E e
  have hg1 : ∀ r : R, g r = r • e := fun r => rfl
  have hg : Function.Surjective g := by
    intro x
    have hx : x ∈ Submodule.span R {e} := by rw [hspan]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨r, hr⟩
  set 𝔞 : Ideal R := LinearMap.ker g with h𝔞
  have hmem𝔞 : ∀ r : R, r ∈ 𝔞 ↔ r • e = 0 := fun r => by rw [h𝔞, LinearMap.mem_ker, hg1]
  let ε : (R ⧸ 𝔞) ≃ₗ[R] E := g.quotKerEquivOfSurjective hg
  have hε : ∀ r : R, ε (Submodule.Quotient.mk r) = r • e := fun r => g.quotKerEquivOfSurjective_apply_mk hg r
  have hεs : ε.symm e = Submodule.Quotient.mk 1 := by
    rw [LinearEquiv.symm_apply_eq, hε, one_smul]

  obtain ⟨N, hN⟩ := hIN
  have hm : 𝔪 ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hN1 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hN
    exact hm (top_le_iff.mp (hN ▸ hI))

  have h𝔞m : 𝔞 ≤ 𝔪 := by
    intro a ha
    by_contra hu
    have hu' : IsUnit a := by by_contra h; exact hu ((IsLocalRing.mem_maximalIdeal a).mpr h)
    have h0 : e = 0 := by
      have := congrArg (fun x => ((hu'.unit⁻¹ : Rˣ) : R) • x) ((hmem𝔞 a).mp ha)
      simpa [smul_smul, IsUnit.val_inv_mul] using this
    exact he (by rw [h0, map_zero])

  have h1 : 𝔞 ≤ I := by
    obtain ⟨φ₀, hφ₀⟩ := ((hW I hI ⟨N, hN⟩).mpr le_rfl) ψ₀
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective I (φ₀ e)
    have hcu : IsUnit c := by
      apply isUnit_of_mk_ne_zero
      rw [← factor_mk hI c, hc, ← LinearMap.comp_apply, hφ₀]
      exact he
    intro a ha
    have h2 : a • φ₀ e = 0 := by rw [← map_smul, (hmem𝔞 a).mp ha, map_zero]
    rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h2
    have := Ideal.mul_mem_right ((hcu.unit⁻¹ : Rˣ) : R) I h2
    rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this

  have h2 : ∀ n : ℕ, I ≤ 𝔞 ⊔ 𝔪 ^ (n + 1) := by
    intro n
    have hJ' : 𝔞 ⊔ 𝔪 ^ (n + 1) ≤ 𝔪 := sup_le h𝔞m (Ideal.pow_le_self (Nat.succ_ne_zero n))
    refine (hW _ hJ' ⟨n + 1, le_sup_right⟩).mp fun ψ => ?_
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective 𝔪 (ψ e)
    refine ⟨c • ((Submodule.factor (le_sup_left : 𝔞 ≤ 𝔞 ⊔ 𝔪 ^ (n + 1))) ∘ₗ ε.symm.toLinearMap), ?_⟩
    apply LinearMap.ext_on hspan
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hεs, factor_mk,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, factor_mk, hc]

  have h3 : I ≤ 𝔞 := by
    intro x hx
    have hkr := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ 𝔞) 𝔪 hm
    have hxm : (Submodule.Quotient.mk x : R ⧸ 𝔞) ∈ ⨅ i : ℕ, (𝔪 ^ i • ⊤ : Submodule R (R ⧸ 𝔞)) := by
      rw [Submodule.mem_iInf]
      intro i
      rcases i with _ | n
      · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
      obtain ⟨a, ha, m, hm', hax⟩ := Submodule.mem_sup.mp (h2 n hx)
      rw [← hax, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero 𝔞).mpr ha, zero_add]
      have : (Submodule.Quotient.mk m : R ⧸ 𝔞) = m • Submodule.Quotient.mk 1 := by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem_smul hm' Submodule.mem_top
    rw [hkr, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hxm
    exact hxm
  have h𝔞I : 𝔞 = I := le_antisymm h1 h3
  exact ⟨ε.symm.trans (Submodule.quotEquivOfEq 𝔞 I h𝔞I)⟩

end Core

section Dict

omit [IsLocalRing R] in
theorem mem_ker_lTensor_iff_baseChange {A : Type u} [CommRing A] [Algebra R A] {K₀ K₁ : Type u}
    [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁] (d : K₀ →ₗ[R] K₁) (z : A ⊗[R] K₀) :
    z ∈ LinearMap.ker (d.lTensor A) ↔ d.baseChange A z = 0 := by
  rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]

end Dict

end SeesawPin29

open SeesawPin29 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : ∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker (d.baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K₀, d.baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K₀, d.baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor K₀ (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    Nonempty ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) ≃ₗ[R] (R ⧸ I)) := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R with h𝔪
  obtain ⟨e, hnat, -⟩ := Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural R K₀ K₁ d
  set E := Module.Dual R K₀ ⧸ LinearMap.range d.dualMap with hE

  obtain ⟨ψ₀, hψ₀, hU'⟩ : ∃ ψ₀ : E →ₗ[R] R ⧸ 𝔪, ψ₀ ≠ 0 ∧ ∀ ψ : E →ₗ[R] R ⧸ 𝔪, ∃ r : R, ψ = r • ψ₀ := by
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI := Module.Free.of_divisionRing (R ⧸ 𝔪) (LinearMap.ker (d.baseChange (R ⧸ 𝔪)))
    obtain ⟨v, hv0, hv⟩ := (finrank_eq_one_iff' (K := R ⧸ 𝔪) (V := LinearMap.ker (d.baseChange (R ⧸ 𝔪)))).mp
      (by convert hU)
    have hvk : (v : (R ⧸ 𝔪) ⊗[R] K₀) ∈ LinearMap.ker (d.lTensor (R ⧸ 𝔪)) := by
      rw [mem_ker_lTensor_iff_baseChange]; exact v.2
    refine ⟨(e (R ⧸ 𝔪)).symm ⟨v, hvk⟩, ?_, fun ψ => ?_⟩
    · intro h
      apply hv0
      have := congrArg (e (R ⧸ 𝔪)) h
      rw [LinearEquiv.apply_symm_apply, map_zero] at this
      exact Subtype.ext (by rw [← Subtype.coe_mk v.1 hvk]; exact congrArg Subtype.val this ▸ rfl)
    · have hψk : ((e (R ⧸ 𝔪) ψ : LinearMap.ker (d.lTensor (R ⧸ 𝔪))) : (R ⧸ 𝔪) ⊗[R] K₀) ∈
          LinearMap.ker (d.baseChange (R ⧸ 𝔪)) := by
        rw [LinearMap.mem_ker, ← mem_ker_lTensor_iff_baseChange]; exact (e (R ⧸ 𝔪) ψ).2
      obtain ⟨c, hc⟩ := hv ⟨_, hψk⟩
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective 𝔪 c
      refine ⟨r, ?_⟩
      apply (e (R ⧸ 𝔪)).injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      have := congrArg Subtype.val hc
      simp only [Submodule.coe_smul] at this
      rw [Submodule.coe_smul]
      rw [← this]
      exact (algebraMap_smul (R ⧸ 𝔪) r (v : (R ⧸ 𝔪) ⊗[R] K₀)).symm

  have hW' : ∀ (J' : Ideal R) (hJ' : J' ≤ 𝔪), (∃ N : ℕ, 𝔪 ^ N ≤ J') →
      ((∀ ψ : E →ₗ[R] R ⧸ 𝔪, ∃ φ : E →ₗ[R] R ⧸ J', (Submodule.factor hJ') ∘ₗ φ = ψ) ↔ I ≤ J') := by
    intro J' hJ' hN
    rw [← hW J' hJ' hN]
    constructor
    · intro H z hz
      have hz' : z ∈ LinearMap.ker (d.lTensor (R ⧸ 𝔪)) := by rw [mem_ker_lTensor_iff_baseChange]; exact hz
      obtain ⟨φ, hφ⟩ := H ((e (R ⧸ 𝔪)).symm ⟨z, hz'⟩)
      refine ⟨(e (R ⧸ J') φ : LinearMap.ker (d.lTensor (R ⧸ J'))), ?_, ?_⟩
      · rw [← mem_ker_lTensor_iff_baseChange]; exact (e (R ⧸ J') φ).2
      · rw [← hnat, hφ, LinearEquiv.apply_symm_apply]
    · intro H ψ
      have hψk : ((e (R ⧸ 𝔪) ψ : LinearMap.ker (d.lTensor (R ⧸ 𝔪))) : (R ⧸ 𝔪) ⊗[R] K₀) ∈
          LinearMap.ker (d.baseChange (R ⧸ 𝔪)) := by
        rw [LinearMap.mem_ker, ← mem_ker_lTensor_iff_baseChange]; exact (e (R ⧸ 𝔪) ψ).2
      obtain ⟨w, hw0, hw⟩ := H _ hψk
      have hw' : w ∈ LinearMap.ker (d.lTensor (R ⧸ J')) := by rw [mem_ker_lTensor_iff_baseChange]; exact hw0
      refine ⟨(e (R ⧸ J')).symm ⟨w, hw'⟩, ?_⟩
      apply (e (R ⧸ 𝔪)).injective
      apply Subtype.ext
      rw [hnat, LinearEquiv.apply_symm_apply]
      exact hw
  exact core I hI hIN ψ₀ hψ₀ hU' hW'

end S_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
end P2MW
export P2MW.S_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff (solution)
