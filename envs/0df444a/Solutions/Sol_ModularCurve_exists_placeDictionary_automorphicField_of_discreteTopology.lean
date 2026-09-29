-- Prove2me | solution 1 for ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/13e361f7-12ff-5a8a-a2df-857474175f35

import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.Analysis.Meromorphic.Order
import Mathlib
import Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
import Theorems.Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem
import Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Topology Manifold
open Filter UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "holRing merRealize merRealize_apply automorphicField mem_automorphicField_iff automorphicField.realize automorphicField.realize_def"
p2m_open "ModularCurve"

namespace HolOrder

theorem analyticAt_comp_ofComplex (f : ↥holRing) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.2).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem analyticOnNhd_comp_ofComplex (f : ↥holRing) :
    AnalyticOnNhd ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.2).analyticOnNhd isOpen_upperHalfPlaneSet

theorem meromorphicAt_comp_ofComplex (f : ↥holRing) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) :=
  (analyticAt_comp_ofComplex f τ).meromorphicAt

theorem eq_zero_of_eventuallyEq_zero (f : ↥holRing) (τ : ℍ)
    (h : (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] 0) : f = 0 := by
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0) subset_rfl (by intro z hz; simp only [Set.mem_setOf_eq] at hz ⊢; exact le_of_lt hz)).isPreconnected
  have hEq := (analyticOnNhd_comp_ofComplex f).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn τ.im_pos h
  apply Subtype.ext
  funext w
  have := hEq w.im_pos
  simp only [ofComplex_apply, Pi.zero_apply] at this
  simpa using this

theorem eventually_ne_zero (f : ↥holRing) (hf : f ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 := by
  rcases (analyticAt_comp_ofComplex f τ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (eq_zero_of_eventuallyEq_zero f τ h) hf
  · exact h

theorem meromorphicOrderAt_ne_top (f : ↥holRing) (hf : f ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  rw [Ne, meromorphicOrderAt_eq_top_iff]
  intro h0
  have := (eventually_ne_zero f hf τ).and h0
  obtain ⟨z, hz1, hz2⟩ := this.exists
  exact hz1 hz2

theorem sec_snd_ne_zero (x : (FractionRing ↥holRing)) :
    ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero _

theorem eq_sec_div (x : (FractionRing ↥holRing)) :
    x = algebraMap ↥holRing (FractionRing ↥holRing) (IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 /
      algebraMap ↥holRing (FractionRing ↥holRing) ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) := by
  rw [eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ↥holRing (FractionRing ↥holRing))).mpr (sec_snd_ne_zero x))]
  exact (IsLocalization.sec_spec (nonZeroDivisors ↥holRing) x)

theorem mul_eq_mul_of_div_eq_div {g h g' h' : ↥holRing} (hh : h ≠ 0) (hh' : h' ≠ 0)
    (e : algebraMap ↥holRing (FractionRing ↥holRing) g / algebraMap ↥holRing (FractionRing ↥holRing) h = algebraMap ↥holRing (FractionRing ↥holRing) g' / algebraMap ↥holRing (FractionRing ↥holRing) h') :
    g * h' = g' * h := by
  have hinj := IsFractionRing.injective ↥holRing (FractionRing ↥holRing)
  rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).mpr hh) ((map_ne_zero_iff _ hinj).mpr hh'),
    ← map_mul, ← map_mul] at e
  exact hinj e

theorem merRealize_comp_ofComplex (x : (FractionRing ↥holRing)) :
    (fun z : ℂ => merRealize x (ofComplex z)) =
      fun z : ℂ => ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 : ℍ → ℂ) (ofComplex z) /
        (((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) : ℍ → ℂ) (ofComplex z) := rfl

theorem meromorphicAt_merRealize (x : (FractionRing ↥holRing)) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) := by
  rw [merRealize_comp_ofComplex]
  exact (meromorphicAt_comp_ofComplex _ τ).div (meromorphicAt_comp_ofComplex _ τ)

theorem merRealize_eventuallyEq_div (x : (FractionRing ↥holRing)) (g h : ↥holRing) (hh : h ≠ 0)
    (hx : x = algebraMap ↥holRing (FractionRing ↥holRing) g / algebraMap ↥holRing (FractionRing ↥holRing) h) (τ : ℍ) :
    (fun z : ℂ => merRealize x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by
  set a := (IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 with ha
  set s : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) with hs
  have hs0 : s ≠ 0 := sec_snd_ne_zero x
  have hrel : a * h = g * s := mul_eq_mul_of_div_eq_div hs0 hh ((eq_sec_div x).symm.trans hx)
  have hpt : ∀ w : ℍ, (a : ℍ → ℂ) w * (h : ℍ → ℂ) w = (g : ℍ → ℂ) w * (s : ℍ → ℂ) w := fun w => by
    have := congrArg (fun f : ↥holRing => (f : ℍ → ℂ) w) hrel
    simpa using this
  filter_upwards [eventually_ne_zero h hh τ, eventually_ne_zero s hs0 τ] with z hz hsz
  rw [merRealize_apply, div_eq_div_iff hsz hz]
  exact hpt (ofComplex z)

theorem meromorphicOrderAt_merRealize_eq_of_eq_div (x : (FractionRing ↥holRing)) (g h : ↥holRing) (hh : h ≠ 0)
    (hx : x = algebraMap ↥holRing (FractionRing ↥holRing) g / algebraMap ↥holRing (FractionRing ↥holRing) h) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) +
        -meromorphicOrderAt (fun z : ℂ => (h : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  rw [meromorphicOrderAt_congr (merRealize_eventuallyEq_div x g h hh hx τ)]
  have e : (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z)) =
      (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) * (fun z : ℂ => (h : ℍ → ℂ) (ofComplex z))⁻¹ := by
    funext z; simp [div_eq_mul_inv]
  rw [e, meromorphicOrderAt_mul (meromorphicAt_comp_ofComplex g τ) (meromorphicAt_comp_ofComplex h τ).inv,
    meromorphicOrderAt_inv]

theorem meromorphicOrderAt_merRealize_mul (x y : (FractionRing ↥holRing)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => merRealize (x * y) (ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) +
        meromorphicOrderAt (fun z : ℂ => merRealize y (ofComplex z)) (τ : ℂ) := by
  set a₁ := (IsLocalization.sec (nonZeroDivisors ↥holRing) x).1
  set s₁ : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing)
  set a₂ := (IsLocalization.sec (nonZeroDivisors ↥holRing) y).1
  set s₂ : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) y).2 : ↥holRing)
  have hs₁ : s₁ ≠ 0 := sec_snd_ne_zero x
  have hs₂ : s₂ ≠ 0 := sec_snd_ne_zero y
  have hxy : x * y = algebraMap ↥holRing (FractionRing ↥holRing) (a₁ * a₂) / algebraMap ↥holRing (FractionRing ↥holRing) (s₁ * s₂) := by
    conv_lhs => rw [eq_sec_div x, eq_sec_div y]
    rw [map_mul, map_mul, div_mul_div_comm]
  have hgerm := merRealize_eventuallyEq_div (x * y) (a₁ * a₂) (s₁ * s₂) (mul_ne_zero hs₁ hs₂) hxy τ
  have hgerm' : (fun z : ℂ => merRealize (x * y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => merRealize x (ofComplex z)) * (fun z : ℂ => merRealize y (ofComplex z)) := by
    filter_upwards [hgerm] with z hz
    rw [hz, Pi.mul_apply, merRealize_apply, merRealize_apply, div_mul_div_comm]
    rfl
  rw [meromorphicOrderAt_congr hgerm',
    meromorphicOrderAt_mul (meromorphicAt_merRealize x τ) (meromorphicAt_merRealize y τ)]

theorem meromorphicOrderAt_merRealize_add (x y : (FractionRing ↥holRing)) (τ : ℍ) :
    min (meromorphicOrderAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ))
        (meromorphicOrderAt (fun z : ℂ => merRealize y (ofComplex z)) (τ : ℂ)) ≤
      meromorphicOrderAt (fun z : ℂ => merRealize (x + y) (ofComplex z)) (τ : ℂ) := by
  set a₁ := (IsLocalization.sec (nonZeroDivisors ↥holRing) x).1
  set s₁ : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing)
  set a₂ := (IsLocalization.sec (nonZeroDivisors ↥holRing) y).1
  set s₂ : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) y).2 : ↥holRing)
  have hs₁ : s₁ ≠ 0 := sec_snd_ne_zero x
  have hs₂ : s₂ ≠ 0 := sec_snd_ne_zero y
  have hinj := IsFractionRing.injective ↥holRing (FractionRing ↥holRing)
  set φ := algebraMap ↥holRing (FractionRing ↥holRing) with hφ
  have H1 : φ s₁ ≠ 0 := (map_ne_zero_iff φ hinj).mpr hs₁
  have H2 : φ s₂ ≠ 0 := (map_ne_zero_iff φ hinj).mpr hs₂
  have hxy : x + y = φ (a₁ * s₂ + s₁ * a₂) / φ (s₁ * s₂) := by
    conv_lhs => rw [eq_sec_div x, eq_sec_div y]
    rw [RingHom.map_add φ, RingHom.map_mul φ, RingHom.map_mul φ, RingHom.map_mul φ, div_add_div _ _ H1 H2]
  have hgerm := merRealize_eventuallyEq_div (x + y) _ (s₁ * s₂) (mul_ne_zero hs₁ hs₂) hxy τ
  have hgerm' : (fun z : ℂ => merRealize (x + y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => merRealize x (ofComplex z)) + (fun z : ℂ => merRealize y (ofComplex z)) := by
    filter_upwards [hgerm, eventually_ne_zero s₁ hs₁ τ, eventually_ne_zero s₂ hs₂ τ] with z hz h1 h2
    rw [hz, Pi.add_apply, merRealize_apply, merRealize_apply, div_add_div _ _ h1 h2]
    rfl
  rw [meromorphicOrderAt_congr hgerm']
  exact meromorphicOrderAt_add (meromorphicAt_merRealize x τ) (meromorphicAt_merRealize y τ)

theorem meromorphicOrderAt_merRealize_algebraMap (c : ℂ) (hc : c ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => merRealize (algebraMap ↥holRing (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c)) (ofComplex z))
      (τ : ℂ) = 0 := by
  classical
  have hx : algebraMap ↥holRing (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c) =
      algebraMap ↥holRing (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c) / algebraMap ↥holRing (FractionRing ↥holRing) 1 := by
    rw [map_one, div_one]
  have hgerm := merRealize_eventuallyEq_div _ _ 1 one_ne_zero hx τ
  have hgerm' : (fun z : ℂ => merRealize (algebraMap ↥holRing (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c)) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => c := by
    filter_upwards [hgerm] with z hz
    rw [hz]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [meromorphicOrderAt_congr hgerm', meromorphicOrderAt_const, if_neg hc]

theorem meromorphicOrderAt_merRealize_eq_top_iff (x : (FractionRing ↥holRing)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) = ⊤ ↔ x = 0 := by
  set a := (IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 with ha
  set s : ↥holRing := ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) with hs
  have hs0 : s ≠ 0 := sec_snd_ne_zero x
  have hinj := IsFractionRing.injective ↥holRing (FractionRing ↥holRing)
  constructor
  · intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop

    have ha0 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (a : ℍ → ℂ) (ofComplex z) = 0 := by
      filter_upwards [htop, eventually_ne_zero s hs0 τ] with z hz hsz
      rw [merRealize_apply, div_eq_zero_iff] at hz
      exact hz.resolve_right hsz
    have ha : a = 0 := by
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := ((eventually_ne_zero a hne τ).and ha0).exists
      exact hz1 hz2
    rw [eq_sec_div x]
    change algebraMap ↥holRing (FractionRing ↥holRing) a / algebraMap ↥holRing (FractionRing ↥holRing) s = 0
    rw [ha, map_zero, zero_div]
  · intro hx0
    rw [meromorphicOrderAt_eq_top_iff]
    have ha : a = 0 := by
      have h := IsLocalization.sec_spec (nonZeroDivisors ↥holRing) x
      have h0 : algebraMap ↥holRing (FractionRing ↥holRing) a = 0 := by
        rw [← h, hx0, zero_mul]
      exact hinj (by rw [map_zero]; exact h0)
    filter_upwards [] with z
    rw [merRealize_apply]
    change (a : ℍ → ℂ) (ofComplex z) / (s : ℍ → ℂ) (ofComplex z) = 0
    rw [ha]
    simp

theorem meromorphicOrderAt_merRealize_ne_top (x : (FractionRing ↥holRing)) (hx : x ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) ≠ ⊤ :=
  fun h => hx ((meromorphicOrderAt_merRealize_eq_top_iff x τ).mp h)

end HolOrder

namespace automorphicField
p2m_export "ModularCurve.automorphicField" "realize realize_def"
p2m_open "ModularCurve.automorphicField"

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]

theorem meromorphicAt_realize (x : ↥(automorphicField Γ)) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ) :=
  HolOrder.meromorphicAt_merRealize _ τ

theorem realize_eventuallyEq_div (x : ↥(automorphicField Γ)) {k : ℤ} (g h : ModularForm Γ k)
    (hh : (h : ℍ → ℂ) ≠ 0)
    (hx : (x : FractionRing ↥holRing) = algebraMap ↥holRing (FractionRing ↥holRing) g.toHolRing /
        algebraMap ↥holRing (FractionRing ↥holRing) h.toHolRing) (τ : ℍ) :
    (fun z : ℂ => realize x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => g (ofComplex z) / h (ofComplex z) :=
  HolOrder.merRealize_eventuallyEq_div _ g.toHolRing h.toHolRing
    (fun e => hh ((ModularForm.toHolRing_eq_zero_iff h).mp e)) hx τ

theorem meromorphicOrderAt_realize_mul (x y : ↥(automorphicField Γ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => realize (x * y) (ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ) +
        meromorphicOrderAt (fun z : ℂ => realize y (ofComplex z)) (τ : ℂ) :=
  HolOrder.meromorphicOrderAt_merRealize_mul _ _ τ

theorem meromorphicOrderAt_realize_add (x y : ↥(automorphicField Γ)) (τ : ℍ) :
    min (meromorphicOrderAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ))
        (meromorphicOrderAt (fun z : ℂ => realize y (ofComplex z)) (τ : ℂ)) ≤
      meromorphicOrderAt (fun z : ℂ => realize (x + y) (ofComplex z)) (τ : ℂ) :=
  HolOrder.meromorphicOrderAt_merRealize_add _ _ τ

theorem meromorphicOrderAt_realize_algebraMap (c : ℂ) (hc : c ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => realize (algebraMap ℂ ↥(automorphicField Γ) c) (ofComplex z)) (τ : ℂ)
      = 0 :=
  HolOrder.meromorphicOrderAt_merRealize_algebraMap c hc τ

theorem meromorphicOrderAt_realize_eq_top_iff (x : ↥(automorphicField Γ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ) = ⊤ ↔ x = 0 := by
  rw [realize_def, HolOrder.meromorphicOrderAt_merRealize_eq_top_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end automorphicField

end ModularCurve

namespace T5

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology.ModularCurve"

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

theorem eventually_ne_zero_of_mem_holRing {s : ℍ → ℂ} (hs : s ∈ holRing) (hs0 : s ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, s z ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ z in 𝓝[≠] τ, s z = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hs0 (UpperHalfPlane.eq_zero_of_frequently hs hfr)

theorem tendsto_smul_nhdsNE (γ : GL (Fin 2) ℝ) (τ : ℍ) :
    Tendsto (fun z : ℍ => γ • z) (𝓝[≠] τ) (𝓝[≠] (γ • τ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_const_smul γ).tendsto τ).mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun z hz => ?_
    intro h
    exact hz (smul_left_cancel γ h)

theorem eventually_nhdsNE_ofComplex_iff {τ : ℍ} {P : ℍ → Prop} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), P (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, P w := by
  rw [eventually_nhdsWithin_iff, eventually_nhdsWithin_iff, ← isOpenEmbedding_coe.map_nhds_eq,
    eventually_map]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    filter_upwards [h] with w hw
    intro hne
    have := hw (fun h' => hne (UpperHalfPlane.ext h'))
    simpa [ofComplex_apply] using this
  · intro h
    filter_upwards [h] with w hw
    intro hne
    have hne' : w ≠ τ := fun h' => hne (congrArg UpperHalfPlane.coe h')
    simpa [ofComplex_apply] using hw hne'

variable [Γ.HasDetOne]

theorem realize_eventuallyEq_div_H (x : ↥(automorphicField Γ)) {k : ℤ} {g h : ModularForm Γ k}
    (hh : (h : ℍ → ℂ) ≠ 0)
    (hx : (x : FractionRing ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
        algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing)
    (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x z = (g : ℍ → ℂ) z / (h : ℍ → ℂ) z :=
  (eventually_nhdsNE_ofComplex_iff (P := fun w => automorphicField.realize x w =
    (g : ℍ → ℂ) w / (h : ℍ → ℂ) w)).1 (automorphicField.realize_eventuallyEq_div x g h hh hx τ)

theorem realize_smul_eventuallyEq (x : ↥(automorphicField Γ)) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : ℍ) : ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x (γ • z) = automorphicField.realize x z := by
  obtain ⟨k, g, h, hh, hx⟩ := (mem_automorphicField_iff (x : FractionRing ↥holRing)).1 x.prop
  have h1 := realize_eventuallyEq_div_H x hh hx τ
  have h2 : ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x (γ • z) = (g : ℍ → ℂ) (γ • z) / (h : ℍ → ℂ) (γ • z) :=
    (tendsto_smul_nhdsNE γ τ).eventually (realize_eventuallyEq_div_H x hh hx (γ • τ))
  have h3 : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) z ≠ 0 := eventually_ne_zero_of_mem_holRing h.holo' hh τ
  filter_upwards [h1, h2, h3] with z h1z h2z h3z
  rw [h2z, h1z, SlashInvariantForm.slash_action_eqn'' g hγ z, SlashInvariantForm.slash_action_eqn'' h hγ z,
    mul_div_mul_left _ _ (zpow_ne_zero k (denom_ne_zero γ z))]

theorem meromorphicOrderAt_realize_smul (x : ↥(automorphicField Γ)) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => automorphicField.realize x (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      meromorphicOrderAt (fun z : ℂ => automorphicField.realize x (ofComplex z)) (τ : ℂ) := by
  have hdet : 0 < (γ : GL (Fin 2) ℝ).val.det := by
    have := congrArg Units.val (Subgroup.HasDetOne.det_eq hγ)
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    rw [this]; exact one_pos
  rw [← meromorphicOrderAt_comp_smul hdet]
  apply meromorphicOrderAt_congr
  exact (eventually_nhdsNE_ofComplex_iff (P := fun w =>
    automorphicField.realize x (γ • w) = automorphicField.realize x w)).2 (realize_smul_eventuallyEq x hγ τ)

def quot {k : ℤ} (g h : ModularForm Γ k) (hh : (h : ℍ → ℂ) ≠ 0) : ↥(automorphicField Γ) :=
  ⟨algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
      algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing, k, g, h, hh, rfl⟩

theorem coe_quot {k : ℤ} (g h : ModularForm Γ k) (hh : (h : ℍ → ℂ) ≠ 0) :
    ((quot g h hh : ↥(automorphicField Γ)) : FractionRing ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
        algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing := rfl

theorem meromorphicOrderAt_realize_quot {k : ℤ} (g h : ModularForm Γ k) (hh : (h : ℍ → ℂ) ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => automorphicField.realize (quot g h hh) (ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z)) (τ : ℂ) :=
  meromorphicOrderAt_congr (automorphicField.realize_eventuallyEq_div _ g h hh (coe_quot g h hh) τ)

theorem exists_analyticOrderAt_eq {k : ℤ} (g : ModularForm Γ k) (hg : (g : ℍ → ℂ) ≠ 0) (τ : ℍ) :
    ∃ n : ℕ, meromorphicOrderAt (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) = (n : ℤ) ∧
      (n = 0 ↔ (g : ℍ → ℂ) τ ≠ 0) := by
  have han : AnalyticAt ℂ (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) :=
    HolOrder.analyticAt_comp_ofComplex g.toHolRing τ
  have hne : meromorphicOrderAt (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ :=
    HolOrder.meromorphicOrderAt_ne_top g.toHolRing (fun e => hg ((ModularForm.toHolRing_eq_zero_iff g).mp e)) τ
  rw [han.meromorphicOrderAt_eq] at hne ⊢
  have hfin : analyticOrderAt (fun z : ℂ => (g : ℍ → ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
    intro h; apply hne; rw [h]; rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨n, by rw [← hn]; rfl, ?_⟩
  have key := han.analyticOrderAt_eq_zero
  simp only [ofComplex_apply] at key
  rw [← key, ← hn]
  exact_mod_cast Iff.rfl

theorem sign_quot {k : ℤ} (g h : ModularForm Γ k) (hg : (g : ℍ → ℂ) ≠ 0) (hh : (h : ℍ → ℂ) ≠ 0) (τ : ℍ) :
    ∃ m : ℤ, meromorphicOrderAt (fun z : ℂ => automorphicField.realize (quot g h hh) (ofComplex z)) (τ : ℂ) = m ∧
      (((g : ℍ → ℂ) τ = 0 → (h : ℍ → ℂ) τ ≠ 0 → 0 < m) ∧
       ((g : ℍ → ℂ) τ ≠ 0 → (h : ℍ → ℂ) τ ≠ 0 → m = 0) ∧
       ((g : ℍ → ℂ) τ ≠ 0 → (h : ℍ → ℂ) τ = 0 → m < 0)) := by
  obtain ⟨a, ha, ha0⟩ := exists_analyticOrderAt_eq g hg τ
  obtain ⟨b, hb, hb0⟩ := exists_analyticOrderAt_eq h hh τ
  have hord := HolOrder.meromorphicOrderAt_merRealize_eq_of_eq_div _ g.toHolRing h.toHolRing
    (fun e => hh ((ModularForm.toHolRing_eq_zero_iff h).mp e)) (coe_quot g h hh) τ
  refine ⟨(a : ℤ) - b, ?_, ?_, ?_, ?_⟩
  · rw [automorphicField.realize_def, hord]
    simp only [ModularForm.coe_toHolRing] at *
    rw [ha, hb]
    rfl
  · intro hgτ hhτ
    have hb' : b = 0 := hb0.mpr hhτ
    have ha' : a ≠ 0 := fun e => (ha0.mp e) hgτ
    omega
  · intro hgτ hhτ
    have hb' : b = 0 := hb0.mpr hhτ
    have ha' : a = 0 := ha0.mpr hgτ
    omega
  · intro hgτ hhτ
    have ha' : a = 0 := ha0.mpr hgτ
    have hb' : b ≠ 0 := fun e => (hb0.mp e) hhτ
    omega

theorem isBoundedUnder_iff_nonneg (x : ↥(automorphicField Γ)) (τ : ℍ) :
    Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖automorphicField.realize x z‖) ↔
      0 ≤ meromorphicOrderAt (fun z : ℂ => automorphicField.realize x (ofComplex z)) (τ : ℂ) := by
  set f : ℂ → ℂ := fun z => automorphicField.realize x (ofComplex z) with hf
  have hmer : MeromorphicAt f (τ : ℂ) := automorphicField.meromorphicAt_realize x τ

  have htrans : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖automorphicField.realize x z‖) ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] (τ : ℂ)) (fun z : ℂ => ‖f z‖) := by
    constructor
    · rintro ⟨M, hM⟩
      rw [eventually_map] at hM
      refine ⟨M, ?_⟩
      rw [eventually_map]
      exact (eventually_nhdsNE_ofComplex_iff (P := fun w => ‖automorphicField.realize x w‖ ≤ M)).2 hM
    · rintro ⟨M, hM⟩
      rw [eventually_map] at hM
      refine ⟨M, ?_⟩
      rw [eventually_map]
      exact (eventually_nhdsNE_ofComplex_iff (P := fun w => ‖automorphicField.realize x w‖ ≤ M)).1 hM
  rw [htrans]
  by_cases htop : meromorphicOrderAt f (τ : ℂ) = ⊤
  · rw [htop]
    refine ⟨fun _ => le_top, fun _ => ?_⟩
    rw [meromorphicOrderAt_eq_top_iff] at htop
    refine ⟨0, ?_⟩
    rw [eventually_map]
    filter_upwards [htop] with z hz
    simp [hz]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨G, hGan, hG0, hfG⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp hn.symm
  rw [← hn]
  constructor
  ·
    intro hbdd
    by_contra hneg
    have hnlt : n < 0 := by
      by_contra h'; exact hneg (by exact_mod_cast not_lt.mp h')
    obtain ⟨M, hM⟩ := hbdd
    rw [eventually_map] at hM

    have hGle : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖G z‖ ≤ M * ‖z - (τ : ℂ)‖ ^ (-n) := by
      filter_upwards [hM, hfG, self_mem_nhdsWithin] with z hMz hfz hzne
      have hz0 : z - (τ : ℂ) ≠ 0 := sub_ne_zero.mpr hzne
      have : G z = (z - (τ : ℂ)) ^ (-n) • f z := by
        rw [hfz, smul_smul, ← zpow_add₀ hz0, neg_add_cancel, zpow_zero, one_smul]
      rw [this, norm_smul, norm_zpow, mul_comm]
      exact mul_le_mul_of_nonneg_right hMz (by positivity)
    have hlim0 : Tendsto (fun z : ℂ => M * ‖z - (τ : ℂ)‖ ^ (-n)) (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => ‖z - (τ : ℂ)‖ ^ (-n)) (𝓝 (τ : ℂ)) (𝓝 0) := by
        obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n)
        rw [hm]
        simp only [zpow_natCast]
        have hm0 : m ≠ 0 := by omega
        simpa [zero_pow hm0] using (tendsto_norm_sub_self (τ : ℂ)).pow m
      simpa using (this.mono_left nhdsWithin_le_nhds).const_mul M
    have hlimG : Tendsto (fun z : ℂ => ‖G z‖) (𝓝[≠] (τ : ℂ)) (𝓝 ‖G τ‖) :=
      (hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).norm
    have := le_of_tendsto_of_tendsto hlimG hlim0 hGle
    exact hG0 (norm_le_zero_iff.mp this)
  ·
    intro h0n
    have h0n' : 0 ≤ n := by exact_mod_cast h0n
    have hlim : Tendsto (fun z : ℂ => ‖(z - (τ : ℂ)) ^ n • G z‖) (𝓝 (τ : ℂ)) (𝓝 ‖((τ : ℂ) - τ) ^ n • G τ‖) := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0n'
      rw [hm]; simp only [zpow_natCast]
      exact (((tendsto_id.sub tendsto_const_nhds).pow m).smul hGan.continuousAt.tendsto).norm
    have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] (τ : ℂ)) (fun z : ℂ => ‖(z - (τ : ℂ)) ^ n • G z‖) :=
      (hlim.mono_left nhdsWithin_le_nhds).isBoundedUnder_le
    obtain ⟨M, hM⟩ := hb
    rw [eventually_map] at hM
    refine ⟨M, ?_⟩
    rw [eventually_map]
    filter_upwards [hM, hfG] with z hMz hfz
    rw [hfz]; exact hMz

end T5

open T5 _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology.ModularCurve in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hsep : ∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ)
    (hloc : ∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) :
    ∃ pt : ℍ → AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ),
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ∈ (pt τ).toValuationSubring ↔
        Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖)) ∧
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ≠ 0 →
        meromorphicOrderAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ) =
          ((((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)) ∧
      (∀ τ τ' : ℍ, pt τ = pt τ' ↔ ∃ γ ∈ Γ, γ • τ = τ') := by
  classical
  have hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1 := fun γ hγ => Subgroup.HasDetOne.det_eq hγ
  let μ : ℍ → ↥(ModularCurve.automorphicField Γ) → WithTop ℤ := fun τ x =>
    meromorphicOrderAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ)
  let e : ℍ → ℕ := fun τ => Nat.card ↥(MulAction.stabilizer ↥Γ τ) / 2

  have he_pos : ∀ τ, 0 < e τ := by
    intro τ
    obtain ⟨hfin, -⟩ := UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ
    haveI := hfin
    obtain ⟨c, hc⟩ := UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ hdet hneg τ
    have hpos : 0 < Nat.card ↥(MulAction.stabilizer ↥Γ τ) := Nat.card_pos
    show 0 < Nat.card ↥(MulAction.stabilizer ↥Γ τ) / 2
    omega

  have he_dvd : ∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)) (n : ℤ), μ τ x = n → ((e τ : ℕ) : ℤ) ∣ n := by
    intro τ x n hn
    have h2n := UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one Γ hdet
      (ModularCurve.automorphicField.realize x) τ (fun γ hγ _ => realize_smul_eventuallyEq x hγ τ) n hn
    obtain ⟨e', he'⟩ := UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ hdet hneg τ
    show ((Nat.card ↥(MulAction.stabilizer ↥Γ τ) / 2 : ℕ) : ℤ) ∣ n
    rw [he', Nat.mul_div_cancel_left _ two_pos]
    rw [he'] at h2n
    push_cast at h2n
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h2n

  have hlocx : ∀ τ : ℍ, ∃ x₀ : ↥(ModularCurve.automorphicField Γ), μ τ x₀ = ((e τ : ℕ) : ℤ) := by
    intro τ
    obtain ⟨k, -, -, g, h, hhτ, hgh⟩ := hloc τ
    have hh : (h : ℍ → ℂ) ≠ 0 := fun e0 => hhτ (by rw [e0]; rfl)
    refine ⟨quot g h hh, ?_⟩
    show meromorphicOrderAt _ _ = _
    rw [meromorphicOrderAt_realize_quot g h hh τ, hgh]

  have hplace : ∀ τ : ℍ, ∃ P : AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ),
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ μ τ x) ∧
      ∀ x, x ≠ 0 → μ τ x = ((((e τ : ℕ) : ℤ) * P.ord x : ℤ) : WithTop ℤ) := by
    intro τ
    obtain ⟨x₀, hx₀⟩ := hlocx τ
    obtain ⟨P, e', he'pos, hval, hord⟩ := AlgebraicCurve.Place.exists_of_orderMap (K := ℂ) (μ τ)
      (fun x => ModularCurve.automorphicField.meromorphicOrderAt_realize_eq_top_iff x τ)
      (fun x y => ModularCurve.automorphicField.meromorphicOrderAt_realize_mul x y τ)
      (fun x y => ModularCurve.automorphicField.meromorphicOrderAt_realize_add x y τ)
      (fun c hc => ModularCurve.automorphicField.meromorphicOrderAt_realize_algebraMap c hc τ)
      ⟨x₀, by rw [hx₀]; exact_mod_cast he_pos τ, by rw [hx₀]; exact WithTop.coe_ne_top⟩
    refine ⟨P, hval, ?_⟩

    have hx₀0 : x₀ ≠ 0 := by
      intro h0
      have := (ModularCurve.automorphicField.meromorphicOrderAt_realize_eq_top_iff x₀ τ).mpr h0
      rw [show meromorphicOrderAt _ _ = μ τ x₀ from rfl, hx₀] at this
      exact WithTop.coe_ne_top this
    have h1 : ((e τ : ℕ) : ℤ) = (e' : ℤ) * P.ord x₀ := by
      have := hord x₀ hx₀0
      rw [hx₀] at this
      exact_mod_cast this
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P.toValuationSubring
    have hπ1 : P.ord (π : ↥(ModularCurve.automorphicField Γ)) = 1 := AlgebraicCurve.Place.ord_coe_irreducible P hπ
    have hπ0 : (π : ↥(ModularCurve.automorphicField Γ)) ≠ 0 := by
      intro h0; exact hπ.ne_zero (Subtype.ext h0)
    have h2 : ((e τ : ℕ) : ℤ) ∣ (e' : ℤ) := by
      have := hord _ hπ0
      rw [hπ1, mul_one] at this
      exact he_dvd τ _ _ this
    have h3 : (e' : ℤ) ∣ ((e τ : ℕ) : ℤ) := ⟨P.ord x₀, h1⟩
    have hee : (e' : ℤ) = ((e τ : ℕ) : ℤ) :=
      Int.dvd_antisymm (by positivity) (by positivity) h3 h2
    intro x hx
    rw [hord x hx, hee]
  choose pt hpt_val hpt_ord using hplace
  refine ⟨pt, ?_, ?_, ?_⟩
  · intro τ x
    rw [hpt_val τ x]
    exact (isBoundedUnder_iff_nonneg x τ).symm
  · intro τ x hx
    exact hpt_ord τ x hx
  · intro τ τ'
    constructor
    ·
      intro hP
      by_contra hne
      have hne' : ∀ γ ∈ Γ, γ • τ ≠ τ' := by
        intro γ hγ h; exact hne ⟨γ, hγ, h⟩
      obtain ⟨k, -, -, g, h, hgh⟩ := hsep τ τ' hne'

      have hsame : ∀ (x : ↥(ModularCurve.automorphicField Γ)) (m m' : ℤ), x ≠ 0 → μ τ x = m → μ τ' x = m' →
          (0 < m ↔ 0 < m') ∧ (m = 0 ↔ m' = 0) := by
        intro x m m' hx hm hm'
        have h1 := hpt_ord τ x hx
        have h2 := hpt_ord τ' x hx
        rw [← hP] at h2
        rw [hm] at h1
        rw [hm'] at h2
        have h1' : m = ((e τ : ℕ) : ℤ) * (pt τ).ord x := by exact_mod_cast h1
        have h2' : m' = ((e τ' : ℕ) : ℤ) * (pt τ).ord x := by exact_mod_cast h2
        have hp1 : (0 : ℤ) < ((e τ : ℕ) : ℤ) := by exact_mod_cast he_pos τ
        have hp2 : (0 : ℤ) < ((e τ' : ℕ) : ℤ) := by exact_mod_cast he_pos τ'
        refine ⟨?_, ?_⟩
        · rw [h1', h2', mul_pos_iff_of_pos_left hp1, mul_pos_iff_of_pos_left hp2]
        · rw [h1', h2', mul_eq_zero, mul_eq_zero, or_iff_right hp1.ne', or_iff_right hp2.ne']

      have hg0 : (g : ℍ → ℂ) ≠ 0 := by
        intro e0; apply hgh; simp [e0]
      have hh0 : (h : ℍ → ℂ) ≠ 0 := by
        intro e0; apply hgh; simp [e0]

      have hfinμ : ∀ (y : ↥(ModularCurve.automorphicField Γ)) (σ : ℍ) (m : ℤ), μ σ y = m → y ≠ 0 := by
        intro y σ m hm h0
        have := (ModularCurve.automorphicField.meromorphicOrderAt_realize_eq_top_iff y σ).mpr h0
        rw [show meromorphicOrderAt _ _ = μ σ y from rfl, hm] at this
        exact WithTop.coe_ne_top this
      by_cases hτ : (h : ℍ → ℂ) τ = 0
      ·
        have hgτ : (g : ℍ → ℂ) τ ≠ 0 := by
          intro e0; apply hgh; rw [hτ, e0, zero_mul, mul_zero]
        have hhτ' : (h : ℍ → ℂ) τ' ≠ 0 := by
          intro e0; apply hgh; rw [hτ, e0, mul_zero, mul_zero]
        obtain ⟨m, hm, s1, s2, s3⟩ := sign_quot h g hh0 hg0 τ
        obtain ⟨m', hm', s1', s2', s3'⟩ := sign_quot h g hh0 hg0 τ'
        have hpos : 0 < m := s1 hτ hgτ
        obtain ⟨hiff, -⟩ := hsame (quot h g hg0) m m' (hfinμ _ τ m hm) hm hm'
        have hpos' : 0 < m' := hiff.mp hpos
        by_cases hgτ' : (g : ℍ → ℂ) τ' = 0
        · exact absurd (s3' hhτ' hgτ') (not_lt.mpr hpos'.le)
        · exact absurd (s2' hhτ' hgτ') hpos'.ne'
      by_cases hτ' : (h : ℍ → ℂ) τ' = 0
      ·
        have hgτ' : (g : ℍ → ℂ) τ' ≠ 0 := by
          intro e0; apply hgh; rw [hτ', e0, zero_mul, mul_zero]
        obtain ⟨m, hm, s1, s2, s3⟩ := sign_quot h g hh0 hg0 τ
        obtain ⟨m', hm', s1', s2', s3'⟩ := sign_quot h g hh0 hg0 τ'
        have hpos' : 0 < m' := s1' hτ' hgτ'
        obtain ⟨hiff, -⟩ := hsame (quot h g hg0) m m' (hfinμ _ τ m hm) hm hm'
        have hpos : 0 < m := hiff.mpr hpos'
        by_cases hgτ : (g : ℍ → ℂ) τ = 0
        · exact absurd (s3 hτ hgτ) (not_lt.mpr hpos.le)
        · exact absurd (s2 hτ hgτ) hpos.ne'
      ·
        set c : ℂ := (g : ℍ → ℂ) τ / (h : ℍ → ℂ) τ with hc
        set g' : ModularForm Γ k := g - c • h with hg'
        have hg'apply : ∀ σ : ℍ, (g' : ℍ → ℂ) σ = (g : ℍ → ℂ) σ - c * (h : ℍ → ℂ) σ := by
          intro σ; simp [hg', smul_eq_mul]
        have hg'τ : (g' : ℍ → ℂ) τ = 0 := by
          rw [hg'apply, hc, div_mul_cancel₀ _ hτ, sub_self]
        have hg'τ' : (g' : ℍ → ℂ) τ' ≠ 0 := by
          rw [hg'apply, hc]
          intro e0
          apply hgh
          rw [sub_eq_zero] at e0
          field_simp at e0
          exact e0.symm
        have hg'0 : (g' : ℍ → ℂ) ≠ 0 := fun e0 => hg'τ' (by rw [e0]; rfl)
        obtain ⟨m, hm, s1, s2, s3⟩ := sign_quot g' h hg'0 hh0 τ
        obtain ⟨m', hm', s1', s2', s3'⟩ := sign_quot g' h hg'0 hh0 τ'
        have hpos : 0 < m := s1 hg'τ hτ
        have hzero' : m' = 0 := s2' hg'τ' hτ'
        obtain ⟨hiff, -⟩ := hsame (quot g' h hh0) m m' (hfinμ _ τ m hm) hm hm'
        exact absurd (hiff.mp hpos) (by rw [hzero']; exact lt_irrefl 0)
    ·
      rintro ⟨γ, hγ, rfl⟩
      apply AlgebraicCurve.Place.ext
      ext x
      rw [hpt_val, hpt_val]
      show 0 ≤ μ τ x ↔ 0 ≤ μ (γ • τ) x
      rw [show μ (γ • τ) x = μ τ x from meromorphicOrderAt_realize_smul x hγ τ]

end
end S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology
end P2MW
export P2MW.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology (solution)
