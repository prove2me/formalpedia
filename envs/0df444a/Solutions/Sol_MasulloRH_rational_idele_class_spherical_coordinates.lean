-- Prove2me | solution 1 for MasulloRH.rational_idele_class_spherical_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:41:17.20033+00:00
-- url     : https://prove2.me/submissions/5b9d1cfd-cd7f-496a-9b9f-2f2814090d7b

import Definitions.Def_MasulloRH_RationalIdeleClass
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_MasulloRH_RationalFiniteRadial
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_MasulloRH_rational_adele_theta_image
import Mathlib

section StandaloneIdeleCoordinates

open NumberField IsDedekindDomain RatIdele MasulloRH.RationalFinite
open scoped Topology
namespace MasulloRH.IdeleCoordinates
noncomputable section

abbrev Ad := AdeleRing (𝓞 ℚ) ℚ
abbrev I := Adˣ
abbrev H := Multiplicative ℝ × K

def principal : ℚˣ →* I := Units.map (algebraMap ℚ Ad).toMonoidHom

private abbrev cyclic_IdeleCoordinates_placeEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The positive real section of the infinite adèles, before applying the exponential. -/
def arch (x : ℝ) : InfiniteAdeleRing ℚ :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) x)

private theorem cyclic_IdeleCoordinates_arch_value (x : ℝ) : cyclic_IdeleCoordinates_placeEquiv (arch x Rat.infinitePlace) = x := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) x)
  exact congrArg (fun z : mixedEmbedding.mixedSpace ℚ => z.1 ⟨Rat.infinitePlace,Rat.isReal_infinitePlace⟩) h

private theorem cyclic_IdeleCoordinates_arch_eval (x : ℝ) : arch x Rat.infinitePlace = cyclic_IdeleCoordinates_placeEquiv.symm x :=
  cyclic_IdeleCoordinates_placeEquiv.toEquiv.eq_symm_apply.mpr (cyclic_IdeleCoordinates_arch_value x)

private theorem cyclic_IdeleCoordinates_continuous_arch : Continuous arch := by
  apply continuous_pi; intro w
  obtain rfl : w=Rat.infinitePlace := Subsingleton.elim _ _
  simp_rw [cyclic_IdeleCoordinates_arch_eval]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous

private theorem cyclic_IdeleCoordinates_arch_mul (a b : ℝ) : arch (a*b) = arch a * arch b := by
  simp only [arch,map_mul]

private theorem cyclic_IdeleCoordinates_arch_one : arch 1 = 1 := by simp only [arch,map_one]

private def cyclic_IdeleCoordinates_vals (h : H) : Ad := (arch (Real.exp h.1.toAdd), (h.2.val : A))

private theorem cyclic_IdeleCoordinates_vals_one : cyclic_IdeleCoordinates_vals 1 = 1 := by
  apply Prod.ext
  · change arch (Real.exp 0) = 1; rw [Real.exp_zero,cyclic_IdeleCoordinates_arch_one]
  · rfl

private theorem cyclic_IdeleCoordinates_vals_mul (x y : H) : cyclic_IdeleCoordinates_vals (x*y) = cyclic_IdeleCoordinates_vals x * cyclic_IdeleCoordinates_vals y := by
  apply Prod.ext
  · change arch (Real.exp (x.1.toAdd + y.1.toAdd)) = _
    rw [Real.exp_add,cyclic_IdeleCoordinates_arch_mul]; rfl
  · rfl

/-- The unique representative with positive real component and integral finite unit component. -/
def rep : H →* I where
  toFun h := ⟨cyclic_IdeleCoordinates_vals h, cyclic_IdeleCoordinates_vals h⁻¹, by rw [← cyclic_IdeleCoordinates_vals_mul,mul_inv_cancel,cyclic_IdeleCoordinates_vals_one], by rw [← cyclic_IdeleCoordinates_vals_mul,inv_mul_cancel,cyclic_IdeleCoordinates_vals_one]⟩
  map_one' := Units.ext cyclic_IdeleCoordinates_vals_one
  map_mul' x y := Units.ext (cyclic_IdeleCoordinates_vals_mul x y)

theorem rep_val (h : H) : (rep h : Ad) = ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) (Real.exp h.1.toAdd)), (h.2.val : A)) := rfl

theorem archCoord_rep (h : H) : archCoord (rep h) = Real.exp h.1.toAdd := cyclic_IdeleCoordinates_arch_value _

theorem finPart_rep (h : H) : finPart (rep h) = h.2.val := Units.ext rfl

private theorem cyclic_IdeleCoordinates_continuous_vals : Continuous cyclic_IdeleCoordinates_vals := by
  exact (cyclic_IdeleCoordinates_continuous_arch.comp (Real.continuous_exp.comp continuous_fst)).prodMk
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd))

theorem continuous_rep : Continuous rep := by
  exact Units.continuous_iff.2 ⟨cyclic_IdeleCoordinates_continuous_vals,cyclic_IdeleCoordinates_continuous_vals.comp continuous_inv⟩

theorem continuous_finPart : Continuous (finPart : I → Aˣ) :=
  (show Continuous (RingHom.snd (InfiniteAdeleRing ℚ) A : Ad → A) from continuous_snd).units_map _

theorem continuous_archCoord : Continuous (archCoord : I → ℝ) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    ((continuous_apply Rat.infinitePlace).comp (continuous_fst.comp Units.continuous_val))

def window : Set I := {x | 0<archCoord x ∧ finPart x ∈ K}

theorem isOpen_window : IsOpen window := by
  have hO := AdelicBox.isOpen_integralFiniteAdeles ℚ
  have hK : IsOpen (K : Set Aˣ) :=
    (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)
  exact (isOpen_lt continuous_const continuous_archCoord).inter (hK.preimage continuous_finPart)

private theorem cyclic_IdeleCoordinates_rep_mem (h : H) : rep h ∈ window :=
  ⟨archCoord_rep h ▸ Real.exp_pos _,finPart_rep h ▸ h.2.property⟩

private def cyclic_IdeleCoordinates_recover (x : window) : H := (Multiplicative.ofAdd (Real.log (archCoord x.val)), ⟨finPart x.val, x.property.2⟩)

private theorem cyclic_IdeleCoordinates_rep_recover (x : window) : rep (cyclic_IdeleCoordinates_recover x) = x.val := by
  apply Units.ext; apply Prod.ext
  · funext w
    obtain rfl : w=Rat.infinitePlace := Subsingleton.elim _ _
    apply cyclic_IdeleCoordinates_placeEquiv.injective
    change archCoord (rep (cyclic_IdeleCoordinates_recover x)) = archCoord x.val
    rw [archCoord_rep]; exact Real.exp_log x.property.1
  · rfl

private theorem cyclic_IdeleCoordinates_recover_rep (h : H) : cyclic_IdeleCoordinates_recover ⟨rep h, cyclic_IdeleCoordinates_rep_mem h⟩ = h := by
  apply Prod.ext
  · change Real.log (archCoord (rep h)) = h.1.toAdd
    rw [archCoord_rep,Real.log_exp]
  · exact Subtype.ext (finPart_rep _)

theorem rep_injective : Function.Injective rep := by
  intro h h' e
  rw [← cyclic_IdeleCoordinates_recover_rep h,← cyclic_IdeleCoordinates_recover_rep h']
  exact congrArg cyclic_IdeleCoordinates_recover (Subtype.ext e)

private def cyclic_IdeleCoordinates_windowEquiv : H ≃ₜ window where
  toFun h := ⟨rep h,cyclic_IdeleCoordinates_rep_mem h⟩
  invFun := cyclic_IdeleCoordinates_recover
  left_inv := cyclic_IdeleCoordinates_recover_rep
  right_inv x := Subtype.ext (cyclic_IdeleCoordinates_rep_recover x)
  continuous_toFun := continuous_rep.subtype_mk _
  continuous_invFun := (Continuous.log (continuous_archCoord.comp continuous_subtype_val)
    (fun x => (archCoord_ne_zero x.val))).prodMk ((continuous_finPart.comp continuous_subtype_val).subtype_mk _)

theorem isOpenMap_rep : IsOpenMap rep :=
  isOpen_window.isOpenEmbedding_subtypeVal.isOpenMap.comp cyclic_IdeleCoordinates_windowEquiv.isOpenMap

/-- The rational principal factor picked by the finite valuations and the real sign. -/
def normalizer : I →* ℚˣ where
  toFun x := Units.mk0 (ρ x) (ρ_ne_zero x)
  map_one' := Units.ext ρ_one
  map_mul' x y := Units.ext (ρ_mul x y)

theorem normalizer_principal (q : ℚˣ) : normalizer (principal q) = q := Units.ext (ρ_principal q)

private theorem cyclic_IdeleCoordinates_window_iff (x : I) : x ∈ window ↔ normalizer x = 1 := by
  constructor
  · rintro ⟨hpos,hfin⟩
    apply Units.ext; change ρ x = 1; apply ρ_eq_of_isNormalizer
    refine ⟨fun v => ?_, by simpa using hpos⟩
    rw [map_one]
    have h1 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hfin.1 v)
    have h2 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hfin.2 v)
    change Valued.v ((x : Ad).2 v) ≤ 1 at h1
    change Valued.v (((x⁻¹ : I) : Ad).2 v) ≤ 1 at h2
    exact le_antisymm h1 (by simpa using (valued_snd_inv_mul x v).symm.le.trans (mul_le_mul_left h2 _))
  · intro hn
    have hρ : ρ x = 1 := congrArg Units.val hn
    have hni : normalizer x⁻¹ = 1 := by rw [map_inv,hn, inv_one]
    have hρi : ρ x⁻¹ = 1 := congrArg Units.val hni
    refine ⟨by simpa [hρ] using (ρ_spec x).2, fun v => ?_, fun v => ?_⟩
    · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr
      change Valued.v ((x : Ad).2 v) ≤ 1
      simpa [hρ] using ((ρ_spec x).1 v).le
    · apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr
      change Valued.v (((x⁻¹ : I) : Ad).2 v) ≤ 1
      simpa [hρi] using ((ρ_spec x⁻¹).1 v).le

theorem normalizer_rep (h : H) : normalizer (rep h) = 1 := (cyclic_IdeleCoordinates_window_iff _).mp (cyclic_IdeleCoordinates_rep_mem h)

theorem exists_principal_rep (x : I) : ∃ q : ℚˣ, ∃ h : H, x=principal q * rep h := by
  let q := normalizer x
  let y := (principal q)⁻¹ * x
  have hw : y ∈ window := (cyclic_IdeleCoordinates_window_iff _).mpr (by simp [y,normalizer_principal,q])
  refine ⟨q,cyclic_IdeleCoordinates_recover ⟨y,hw⟩,?_⟩
  rw [cyclic_IdeleCoordinates_rep_recover]; exact (mul_inv_cancel_left (principal q) x).symm

theorem rep_mem_principal (h : H) (hm : rep h ∈ principal.range) : h=1 := by
  obtain ⟨q,hq⟩ := hm
  have hq1 : q=1 := (normalizer_principal q).symm.trans ((congrArg normalizer hq).trans (normalizer_rep h))
  apply rep_injective; rw [← hq,hq1, map_one, map_one]

theorem principal_factors (x : I) : ∃ p ∈ principal.range, ∃ h : H, x=p*rep h := by
  obtain ⟨q,h,he⟩ := exists_principal_rep x
  exact ⟨principal q,⟨q,rfl⟩,h,he⟩

end
end MasulloRH.IdeleCoordinates

end StandaloneIdeleCoordinates

section StandaloneIdeleCoordinatesNorm

open NumberField RatIdele MasulloRH.RationalFinite MeasureTheory
open scoped Topology
namespace MasulloRH.IdeleCoordinates
noncomputable section

private theorem cyclic_IdeleCoordinatesNorm_unit_compact : CompactSpace K := by
  let S : Set (A×A) := (O ×ˢ O) ∩ {z | z.1*z.2=1}
  have hc : IsCompact S := (AdelicBox.isCompact_integralFiniteAdeles ℚ).prod
    (AdelicBox.isCompact_integralFiniteAdeles ℚ) |>.inter_right
    (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  let f (z : S) : Aˣ := ⟨z.val.1,z.val.2,z.prop.2, (mul_comm _ _).trans z.prop.2⟩
  let F (z : S) : K := ⟨f z,z.prop.1⟩
  have h : Continuous f := Units.continuous_iff.mpr
    ⟨continuous_fst.comp continuous_subtype_val,continuous_snd.comp continuous_subtype_val⟩
  have hF : Continuous F := h.subtype_mk _
  have hsurj : Function.Surjective F := by
    intro u
    exact ⟨⟨((u.val:A),↑u.val⁻¹),u.prop,Units.mul_inv u.val⟩,Subtype.ext (Units.ext rfl)⟩
  exact hsurj.compactSpace hF

/-- The actual Tate modulus as a positive real monoid homomorphism on rational idèles. -/
def tateNorm : I →* ℝ where
  toFun := TateGlobal.ideleNorm ℚ
  map_one' := by
    have h : TateGlobal.ideleNorm ℚ (1:I) * TateGlobal.ideleNorm ℚ 1
        = TateGlobal.ideleNorm ℚ (1:I)*1 := by rw [mul_one,← TateGlobal.ideleNorm_mul, one_mul]
    exact mul_left_cancel₀ (TateGlobal.ideleNorm_pos _).ne' h
  map_mul' := TateGlobal.ideleNorm_mul

theorem tateNorm_principal (q : ℚˣ) : tateNorm (principal q) = 1 := by
  let : MeasurableSpace Ad := borel Ad
  let : BorelSpace Ad := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ q
  change ((distribHaarChar Ad (Units.map (algebraMap ℚ Ad).toMonoidHom q) : NNReal) : ℝ) = 1
  rw [h,NNReal.coe_one]

private theorem cyclic_IdeleCoordinatesNorm_tateNorm_arch (s : Multiplicative ℝ) :
    tateNorm (rep (s,1)) = Real.exp s.toAdd := by
  change ((distribHaarChar Ad (rep (s,1)) : NNReal) : ℝ) = _
  have hs : ((rep (s,1) : I) : Ad).2 = 1 := rfl
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one ℚ _ hs,
    Fintype.prod_unique]
  have hm : Rat.infinitePlace.mult = 1 := InfinitePlace.mult_isReal ⟨_, Rat.isReal_infinitePlace⟩
  change ‖((rep (s,1):I):Ad).1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult = _
  rw [hm, pow_one]
  let E := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have he : E (((rep (s,1):I):Ad).1 Rat.infinitePlace) = Real.exp s.toAdd := archCoord_rep (s,1)
  rw [← E.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace)), he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

private theorem cyclic_IdeleCoordinatesNorm_tateNorm_unit (u : K) : tateNorm (rep (1,u)) = 1 := by
  let : CompactSpace K := cyclic_IdeleCoordinatesNorm_unit_compact
  let m : K →* ℝ := (tateNorm.comp rep).comp (MonoidHom.inr (Multiplicative ℝ) K)
  have hm : Continuous m := (TateGlobal.continuous_ideleNorm ℚ).comp
    (continuous_rep.comp (continuous_const.prodMk continuous_id))
  have hp (v : K) : 0 < m v := TateGlobal.ideleNorm_pos _
  obtain ⟨B,hB⟩ := (isCompact_range hm).bddAbove
  have hle (v : K) : m v ≤ B := hB ⟨v,rfl⟩
  have hkey (v : K) : m v ≤ 1 := by
    by_contra hgt
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hgt)
    have hn' := hle (v^n)
    rw [map_pow] at hn'
    exact (not_lt_of_ge hn') hn
  have hi := hkey u⁻¹
  rw [map_inv] at hi
  exact le_antisymm (hkey u) ((inv_le_one₀ (hp u)).1 hi)

theorem ideleNorm_rep (h : H) : TateGlobal.ideleNorm ℚ (rep h) = Real.exp h.1.toAdd := by
  change tateNorm (rep h) = _
  have he : (h.1, (1:K)) * ((1:Multiplicative ℝ), h.2) = h := by ext <;> simp
  conv_lhs => rw [← he]
  rw [map_mul, map_mul, cyclic_IdeleCoordinatesNorm_tateNorm_unit, mul_one, cyclic_IdeleCoordinatesNorm_tateNorm_arch]

theorem ideleNorm_eq_of_factor {x : I} (q : ℚˣ) (h : H) (hx : x=principal q * rep h) :
    TateGlobal.ideleNorm ℚ x = Real.exp h.1.toAdd := by
  change tateNorm x = _
  rw [hx,map_mul,tateNorm_principal,one_mul]
  exact ideleNorm_rep h

theorem ideleNorm_normalized (x : I) : TateGlobal.ideleNorm ℚ x = archCoord x / ((ρ x : ℚ):ℝ) := by
  obtain ⟨q,h,hx⟩ := exists_principal_rep x
  have hn : normalizer x = q := by rw [hx,map_mul,normalizer_principal,normalizer_rep,mul_one]
  have hr : ρ x=(q:ℚ) := congrArg Units.val hn
  rw [ideleNorm_eq_of_factor q h hx,hr,hx,archCoord_mul,show archCoord (principal q)=((q:ℚ):ℝ) from archCoord_principal q,archCoord_rep]
  have hnq : ((q:ℚ):ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  field_simp [hnq]

/-- The Tate modulus descended through the full rational principal subgroup. -/
def quotientNorm : (I ⧸ principal.range) →* ℝ :=
  QuotientGroup.lift principal.range tateNorm (by
    rintro _ ⟨q,rfl⟩
    exact tateNorm_principal q)

theorem quotientNorm_mk (x : I) : quotientNorm (QuotientGroup.mk x) = TateGlobal.ideleNorm ℚ x := rfl

theorem compact_quotientNorm_ker : CompactSpace quotientNorm.ker := by
  let : CompactSpace K := cyclic_IdeleCoordinatesNorm_unit_compact
  let mk := QuotientGroup.mk' principal.range
  let f (u : K) := mk (rep (1,u))
  have hf (u : K) : f u ∈ quotientNorm.ker := by
    change TateGlobal.ideleNorm ℚ (rep (1,u)) = 1
    rw [ideleNorm_rep]; exact Real.exp_zero
  let F (u : K) : quotientNorm.ker := ⟨f u,hf u⟩
  have hF : Continuous F := (QuotientGroup.continuous_mk.comp
    (continuous_rep.comp (continuous_const.prodMk continuous_id))).subtype_mk _
  refine Function.Surjective.compactSpace (f:=F) hF ?_
  intro y
  obtain ⟨x,hx⟩ := QuotientGroup.mk_surjective y.val
  obtain ⟨q,h,hq⟩ := exists_principal_rep x
  have hnorm : Real.exp h.1.toAdd = 1 := by
    rw [← ideleNorm_eq_of_factor q h hq,← quotientNorm_mk,hx]
    exact y.property
  have hfst : h.1=1 := Real.exp_injective (hnorm.trans Real.exp_zero.symm)
  refine ⟨h.2,Subtype.ext ?_⟩
  change mk (rep (1,h.2))=y.val
  rw [← hx,hq]
  change mk (rep (1,h.2))=mk (principal q * rep h)
  rw [map_mul,show mk (principal q)=1 from (QuotientGroup.eq_one_iff _).mpr ⟨q,rfl⟩,one_mul (mk (rep h))]
  congr 2
  exact Prod.ext hfst.symm rfl

end
end MasulloRH.IdeleCoordinates

end StandaloneIdeleCoordinatesNorm

section StandaloneIdeleOrbitDescent

open NumberField IsDedekindDomain MeasureTheory MasulloRH.RationalFinite
open scoped BigOperators Topology SchwartzMap

namespace MasulloRH.IdeleOrbit
noncomputable section

abbrev Ad := AdeleRing (𝓞 ℚ) ℚ
abbrev principals : Subgroup Adˣ := (Units.map (algebraMap ℚ Ad : ℚ →* Ad)).range
abbrev C := Adˣ ⧸ principals

def summandOrbit (F : Ad → ℂ) (z : Adˣ) : ℂ :=
  ∑' q : ℚ, F ((z : Ad) * algebraMap ℚ Ad q)

theorem orbit_principal_mul (F : Ad → ℂ) (q : ℚˣ) (z : Adˣ) :
    summandOrbit F (Units.map (algebraMap ℚ Ad : ℚ →* Ad) q * z) = summandOrbit F z := by
  let m : Equiv.Perm ℚ := MulAction.toPerm q
  calc
    _ = ∑' j : ℚ, F ((z : Ad) * algebraMap ℚ Ad (m j)) := by
      apply tsum_congr
      intro j
      change F ((algebraMap ℚ Ad (q:ℚ) * (z:Ad)) * algebraMap ℚ Ad j) =
        F ((z : Ad) * algebraMap ℚ Ad ((q:ℚ)*j))
      rw [map_mul]
      congr 1
      ring
    _ = _ := m.tsum_eq (fun j : ℚ => F ((z : Ad) * algebraMap ℚ Ad j))

private theorem cyclic_IdeleOrbitDescent_orbit_eq_of_mk_eq (F : Ad → ℂ) {x y : Adˣ}
    (h : (x : C) = (y : C)) : summandOrbit F x = summandOrbit F y := by
  obtain ⟨q,hq⟩ := QuotientGroup.eq_iff_div_mem.mp h
  have hxy : x = Units.map (algebraMap ℚ Ad : ℚ →* Ad) q * y :=
    by rw [hq, div_mul_cancel]
  exact hxy ▸ orbit_principal_mul F q y

def descend (F : Ad → ℂ) : C → ℂ :=
  Quotient.lift (summandOrbit F) (fun _ _ h => cyclic_IdeleOrbitDescent_orbit_eq_of_mk_eq F (Quotient.sound h))

theorem descend_mk (F : Ad → ℂ) (x : Adˣ) : descend F (x : C) = summandOrbit F x := rfl

theorem unique_descent (F : Ad → ℂ) :
    ∃! Φ : C → ℂ, ∀ x : Adˣ, Φ (x : C) = ∑' q : ℚ, F ((x : Ad) * algebraMap ℚ Ad q) := by
  refine ⟨descend F,descend_mk F,?_⟩
  intro Ψ hΨ
  funext x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective principals x
  exact hΨ x

end
end MasulloRH.IdeleOrbit

end StandaloneIdeleOrbitDescent

section StandaloneIdeleClassSpherical

open NumberField IsDedekindDomain MeasureTheory MasulloRH.RationalFinite
open scoped SchwartzMap Topology
namespace MasulloRH.IdeleOrbit
noncomputable section

abbrev H := Multiplicative ℝ × K
def radial (t : ℝ) (u : K) (q : ℚ) : Ad :=
  let d : Ad := ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) t), (u.val : A))
  d * algebraMap ℚ Ad q

def projected [MeasurableSpace K] (κ : Measure K) (e : H ≃ₜ* C) (F : Ad → ℂ) (z : C) : ℂ :=
  ∫ u : K, descend F (z*e (1,u)) ∂κ

theorem projected_eq_radial [MeasurableSpace K] [BorelSpace K] (κ : Measure K)
    [κ.IsMulLeftInvariant] (e : H ≃ₜ* C)
    (he : ∀ h : H, e h = ((IdeleCoordinates.rep h : Adˣ) : C))
    (F : Ad → ℂ) (z : C) :
    projected κ e F z = ∫ u : K, ∑' q : ℚ, F (radial (Real.exp (e.symm z).1.toAdd) u q) ∂κ := by
  obtain ⟨⟨s,v⟩,rfl⟩ := e.surjective z
  rw [e.symm_apply_apply]
  unfold projected
  calc
    _ = ∫ u : K, ∑' q : ℚ, F (radial (Real.exp s.toAdd) (v*u) q) ∂κ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      change descend F (e (s,v)*e (1,u)) = _
      have hm : e (s,v) * e (1,u) = e ((s,v)*(1,u)) := (map_mul e _ _).symm
      rw [hm,he,descend_mk]
      change (∑' q : ℚ, F (radial (Real.exp (s*1).toAdd) (v*u) q)) = _
      rw [mul_one]
    _ = _ := integral_mul_left_eq_self (fun u : K => ∑' q : ℚ, F (radial (Real.exp s.toAdd) u q)) v

theorem image [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ]
    (e : H ≃ₜ* C) (he : ∀ h : H, e h = ((IdeleCoordinates.rep h : Adˣ) : C)) :
    {Φ : C → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0 = 0 ∧ (∫ a, F a ∂μ) = 0 ∧
        Φ = projected κ e F} =
    {Φ : C → ℂ | ∃ g : 𝓢(ℝ,ℂ), g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧
        ∀ z, Φ z = ∑' n : ℤ, g ((n:ℝ)*Real.exp (e.symm z).1.toAdd)} := by
  have himg := (rational_adele_theta_image μ κ).2.2
  ext Φ
  constructor
  · rintro ⟨F,hF,h0,hI,rfl⟩
    let φ (t : {t : ℝ // 0<t}) := ∫ u : K, ∑' q : ℚ, F (radial t.val u q) ∂κ
    have hh : ∃ g : 𝓢(ℝ,ℂ), g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧
        ∀ t, φ t = ∑' n : ℤ, g ((n:ℝ)*t.val) := by
      exact (Set.ext_iff.mp himg φ).1 (show φ ∈ {Φ : {t : ℝ // 0<t} → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ,
        F 0 = 0 ∧ (∫ x, F x ∂μ) = 0 ∧ ∀ t, Φ t = ∫ u : K, ∑' q : ℚ, F (radial t.val u q) ∂κ} from
        ⟨F,hF,h0,hI,fun _ => rfl⟩)
    obtain ⟨g,hg0,hgI,hg⟩ := hh
    exact ⟨g,hg0,hgI,fun z => (projected_eq_radial κ e he F z).trans (hg ⟨_,Real.exp_pos _⟩)⟩
  · rintro ⟨g,hg0,hgI,hg⟩
    let ψ (t : {t : ℝ // 0<t}) := ∑' n : ℤ, g ((n:ℝ)*t.val)
    have hh : ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0 = 0 ∧ (∫ x, F x ∂μ) = 0 ∧
        ∀ t, ψ t = ∫ u : K, ∑' q : ℚ, F (radial t.val u q) ∂κ := by
      exact (Set.ext_iff.mp himg ψ).2 (show ψ ∈ {Φ : {t : ℝ // 0<t} → ℂ | ∃ g : 𝓢(ℝ,ℂ),
        g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧ ∀ t, Φ t = ∑' n : ℤ, g ((n:ℝ)*t.val)} from
        ⟨g,hg0,hgI,fun _ => rfl⟩)
    obtain ⟨F,hF,h0,hI,hψ⟩ := hh
    exact ⟨F,hF,h0,hI,funext fun z => (hg z).trans ((hψ ⟨_,Real.exp_pos _⟩).trans
      (projected_eq_radial κ e he F z).symm)⟩
end
end MasulloRH.IdeleOrbit

end StandaloneIdeleClassSpherical

section StandaloneIdeleQuotient

open Set MeasureTheory Topology
open scoped ENNReal
namespace MasulloRH.IdeleQuotient
noncomputable section

section Representatives
variable {G H : Type*} [CommGroup G] [Group H]

/-- An element is determined modulo the principal subgroup by its complement coordinate. -/
theorem bijective_mk_of_factors (P : Subgroup G) (r : H →* G)
    (hker : ∀ h : H, r h ∈ P → h=1)
    (hfac : ∀ g : G, ∃ p ∈ P, ∃ h : H, g=p*r h) :
    Function.Bijective ((QuotientGroup.mk' P).comp r) := by
  constructor
  · intro a b hab
    have hm : r (a/b) ∈ P := (map_div r a b) ▸ (QuotientGroup.eq_iff_div_mem.mp hab)
    exact div_eq_one.mp (hker _ hm)
  · intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨p,hp,h,rfl⟩ := hfac g
    refine ⟨h,?_⟩
    change (QuotientGroup.mk' P) (r h) = (QuotientGroup.mk' P) (p*r h)
    rw [map_mul,show (QuotientGroup.mk' P) p=1 from (QuotientGroup.eq_one_iff _).mpr hp,one_mul]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]

/-- A continuous and open parameterization by unique coset representatives identifies
the parameter group topologically and multiplicatively with the quotient. -/
def chart (P : Subgroup G) (r : H →* G) (hc : Continuous r) (ho : IsOpenMap r)
    (hb : Function.Bijective ((QuotientGroup.mk' P).comp r)) : H ≃ₜ* (G ⧸ P) := by
  let e : H ≃* (G ⧸ P) := MulEquiv.ofBijective _ hb
  have hce : Continuous e := QuotientGroup.continuous_mk.comp hc
  have hoe : IsOpenMap e := QuotientGroup.isOpenMap_coe.comp ho
  exact { e, e.toEquiv.toHomeomorphOfContinuousOpen hce hoe with }

@[simp] theorem chart_apply (P : Subgroup G) (r : H →* G) (hc ho hb) (h : H) :
    chart P r hc ho hb h = (QuotientGroup.mk' P) (r h) := rfl

/-- The open-subgroup version of the chart. -/
def subgroupChart (P L : Subgroup G) (hopen : IsOpen (L:Set G))
    (hker : ∀ g ∈ L, g ∈ P → g = 1)
    (hfac : ∀ g : G, ∃ p ∈ P, ∃ l ∈ L, g=p*l) : L ≃ₜ* (G ⧸ P) :=
  chart P L.subtype continuous_subtype_val hopen.isOpenMap_subtype_val
    (bijective_mk_of_factors P L.subtype (fun h hp => Subtype.ext (hker h h.prop hp))
      (fun g => by obtain ⟨p,hp,l,hl,he⟩ := hfac g; exact ⟨p,hp,⟨l,hl⟩,he⟩))

end Representatives

section LogHaar
variable {K C : Type*} [Group K] [TopologicalSpace K] [Group C] [TopologicalSpace C]

/-- The chart with its logarithmic parameter written as an additive real number. -/
def realChart (e : Multiplicative ℝ × K ≃ₜ* C) : (ℝ × K) ≃ₜ C :=
  e.toHomeomorph

@[simp] theorem realChart_apply (e : Multiplicative ℝ × K ≃ₜ* C) (x : ℝ) (u : K) :
    realChart e (x,u) = e (Multiplicative.ofAdd x,u) := rfl

variable [MeasurableSpace K] [BorelSpace K] [MeasurableSpace C] [BorelSpace C]

/-- The class Haar measure normalized to Lebesgue measure in the log coordinate
and to the chosen Haar measure on the norm-one subgroup. -/
def logProductHaar (κ : Measure K) (e : Multiplicative ℝ × K ≃ₜ* C) : Measure C :=
  Measure.map (realChart e) ((volume : Measure ℝ).prod κ)

theorem realChart_measurePreserving (κ : Measure K) (e : Multiplicative ℝ × K ≃ₜ* C) :
    MeasurePreserving (realChart e) ((volume : Measure ℝ).prod κ) (logProductHaar κ e) :=
  ⟨(realChart e).continuous.measurable,rfl⟩

/-- Existence of Haar measure after transport includes its left invariance, positivity on
open sets and finiteness on compact sets. -/
theorem logProductHaar_isHaarMeasure [IsTopologicalGroup K] [IsTopologicalGroup C] (κ : Measure K) [κ.IsHaarMeasure] [SFinite κ]
    (e : Multiplicative ℝ × K ≃ₜ* C) : (logProductHaar κ e).IsHaarMeasure := by
  let : MeasurableSpace (Multiplicative ℝ) := Real.measurableSpace
  let : BorelSpace (Multiplicative ℝ) := inferInstanceAs (BorelSpace ℝ)
  let logVolume : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : logVolume.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
      toIsOpenPosMeasure := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
      map_mul_left_eq_self := fun x => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := (volume : Measure ℝ)) x.toAdd }
  exact e.isHaarMeasure_map (logVolume.prod κ)

/-- A translation-invariant probability on a compact group is Haar in the full sense. -/
theorem haarProbability_of_compact [IsTopologicalGroup K] [CompactSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    κ.IsHaarMeasure := by
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior κ (Set.univ:Set K) isCompact_univ
  all_goals simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrate on the quotient by first taking the compact orbit average and then the
Lebesgue integral of the log-norm variable. -/
theorem integral_logProductHaar (κ : Measure K) [SFinite κ] (e : Multiplicative ℝ × K ≃ₜ* C)
    (F : C → E) (hF : Integrable F (logProductHaar κ e)) :
    (∫ c : C, F c ∂logProductHaar κ e) =
      ∫ x : ℝ, ∫ u : K, F (e (Multiplicative.ofAdd x,u)) ∂κ := by
  have h := realChart_measurePreserving κ e
  calc
    _ = ∫ p : ℝ × K, F (realChart e p) ∂(volume.prod κ) :=
      (h.integral_comp (realChart e).toMeasurableEquiv.measurableEmbedding _).symm
    _ = _ := integral_prod _ (h.integrable_comp_of_integrable hF)

/-- Every log interval of length one over the full norm-one fiber has mass one. -/
theorem logProductHaar_slab (κ : Measure K) [IsProbabilityMeasure κ]
    (e : Multiplicative ℝ × K ≃ₜ* C) (a b : ℝ) :
    logProductHaar κ e ((realChart e) '' (Icc a b ×ˢ (univ:Set K))) = ENNReal.ofReal (b-a) := by
  let q := (realChart e).toMeasurableEquiv
  change Measure.map q ((volume : Measure ℝ).prod κ) (q '' (Icc a b ×ˢ univ)) = _
  rw [q.measurableEmbedding.map_apply]
  rw [Set.preimage_image_eq _ q.injective,Measure.prod_prod,Real.volume_Icc,measure_univ,mul_one]

/-- The quotient log norm has exactly Lebesgue measure as its pushforward. -/
theorem log_norm_measurePreserving (κ : Measure K) [IsProbabilityMeasure κ]
    (e : Multiplicative ℝ × K ≃ₜ* C) :
    MeasurePreserving (fun q : C => (e.symm q).1.toAdd) (logProductHaar κ e) (volume : Measure ℝ) := by
  let q := (realChart e).toMeasurableEquiv
  have h : MeasurePreserving q ((volume : Measure ℝ).prod κ) (logProductHaar κ e) :=
    realChart_measurePreserving κ e
  exact (measurePreserving_fst (μ := (volume : Measure ℝ)) (ν := κ)).comp h.symm

end LogHaar
end
end MasulloRH.IdeleQuotient

end StandaloneIdeleQuotient

section StandaloneIdeleQuotientRational

open NumberField IsDedekindDomain MeasureTheory Set TopologicalSpace
open MasulloRH.RationalFinite MasulloRH.IdeleQuotient
open scoped Topology ENNReal
namespace MasulloRH.IdeleCoordinates
noncomputable section

abbrev Classes := I ⧸ principal.range

def quotientChart : H ≃ₜ* Classes :=
  chart principal.range rep continuous_rep isOpenMap_rep
    (bijective_mk_of_factors principal.range rep rep_mem_principal principal_factors)

@[simp] theorem quotientChart_apply (h : H) :
    quotientChart h = (QuotientGroup.mk' principal.range) (rep h) := rfl

/-- In the logarithmic coordinates of the canonical positive representative,
this is the real log-norm coordinate on the idèle class group. -/
def quotientLog (q : Classes) : ℝ := (quotientChart.symm q).1.toAdd

@[simp] theorem quotientLog_mk_rep (h : H) :
    quotientLog ((QuotientGroup.mk' principal.range) (rep h)) = h.1.toAdd := by
  change (quotientChart.symm (quotientChart h)).1.toAdd = _
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem compact_finite_idelic_units : CompactSpace K := by
  let S : Set (A×A) := (O ×ˢ O) ∩ {z | z.1*z.2=1}
  have hc : IsCompact S := (AdelicBox.isCompact_integralFiniteAdeles ℚ).prod
    (AdelicBox.isCompact_integralFiniteAdeles ℚ) |>.inter_right
      (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  let f (z : S) : Aˣ := ⟨z.val.1,z.val.2,z.prop.2, (mul_comm _ _).trans z.prop.2⟩
  let F (z : S) : K := ⟨f z,z.prop.1⟩
  have h : Continuous f := Units.continuous_iff.mpr
    ⟨continuous_fst.comp continuous_subtype_val,continuous_snd.comp continuous_subtype_val⟩
  have hF : Continuous F := h.subtype_mk _
  have hsurj : Function.Surjective F := by
    intro u
    exact ⟨⟨((u.val:A),↑u.val⁻¹),u.prop,Units.mul_inv u.val⟩,Subtype.ext (Units.ext rfl)⟩
  exact hsurj.compactSpace hF

section Units
variable [MeasurableSpace K] [BorelSpace K]

theorem exists_unit_haar_probability : ∃ κ : Measure K, κ.IsHaarMeasure ∧ IsProbabilityMeasure κ := by
  let : CompactSpace K := compact_finite_idelic_units
  let U : PositiveCompacts K := ⟨⟨univ,isCompact_univ⟩,by simp⟩
  exact ⟨Measure.haarMeasure U,inferInstance,⟨Measure.haarMeasure_self (K₀:=U)⟩⟩

theorem unit_probability_isHaarMeasure (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    κ.IsHaarMeasure := by
  let : CompactSpace K := compact_finite_idelic_units
  exact haarProbability_of_compact κ

end Units

variable [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Classes] [BorelSpace Classes]

/-- Haar measure of the actual quotient of the rational ideles by the principal subgroup. -/
def quotientHaar (κ : Measure K) : Measure Classes := logProductHaar κ quotientChart

theorem quotientHaar_isHaarMeasure (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    (quotientHaar κ).IsHaarMeasure := by
  let : κ.IsHaarMeasure := unit_probability_isHaarMeasure κ
  exact logProductHaar_isHaarMeasure κ quotientChart

theorem quotientChart_measurePreserving (κ : Measure K) :
    MeasurePreserving (fun p : ℝ × K => (QuotientGroup.mk' principal.range)
      (rep (Multiplicative.ofAdd p.1,p.2))) ((volume : Measure ℝ).prod κ) (quotientHaar κ) :=
  realChart_measurePreserving κ quotientChart

theorem quotientLog_measurePreserving (κ : Measure K) [IsProbabilityMeasure κ] :
    MeasurePreserving quotientLog (quotientHaar κ) (volume : Measure ℝ) :=
  log_norm_measurePreserving κ quotientChart

theorem quotientHaar_slab (κ : Measure K) [IsProbabilityMeasure κ] (a b : ℝ) :
    quotientHaar κ ((fun p : ℝ × K => (QuotientGroup.mk' principal.range)
      (rep (Multiplicative.ofAdd p.1,p.2))) '' (Icc a b ×ˢ univ)) = ENNReal.ofReal (b-a) :=
  logProductHaar_slab κ quotientChart a b

theorem integral_quotientHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Measure K) [SFinite κ] (F : Classes → E) (hF : Integrable F (quotientHaar κ)) :
    (∫ q : Classes, F q ∂quotientHaar κ) =
      ∫ x : ℝ, ∫ u : K, F ((QuotientGroup.mk' principal.range) (rep (Multiplicative.ofAdd x,u))) ∂κ :=
  integral_logProductHaar κ quotientChart F hF

end
end MasulloRH.IdeleCoordinates

end StandaloneIdeleQuotientRational

section StandaloneIdeleSphericalL2

open MeasureTheory Set Filter NumberField
open MasulloRH.RationalFinite MasulloRH.IdeleCoordinates
open scoped InnerProductSpace Topology
namespace MasulloRH.IdeleSphericalL2
noncomputable section

/-- Taking the mean over a probability fiber contracts the squared norm. -/
private theorem cyclic_IdeleSphericalL2_mean_sq_bound {K : Type*} [MeasurableSpace K] (κ : Measure K) [IsProbabilityMeasure κ]
    {f : K → ℂ} (hf : MemLp f 2 κ) :
    ‖∫ k, f k ∂κ‖^2 ≤ ∫ k, ‖f k‖^2 ∂κ := by
  have hi := hf.integrable (by norm_num)
  have hs := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 2).trans
    ((convexOn_pow 2).map_integral_le (continuousOn_pow 2) isClosed_Ici
      (ae_of_all _ fun _ => norm_nonneg _) hi.norm hs)

theorem fiber_mean_memLp {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
    {μ : Measure X} [SFinite μ] (κ : Measure K) [IsProbabilityMeasure κ]
    {F : X × K → ℂ} (hF : StronglyMeasurable F) (hp : MemLp F 2 (μ.prod κ)) :
    (∀ᵐ x ∂μ, Integrable (fun k => F (x,k)) κ) ∧
      MemLp (fun x => ∫ k, F (x,k) ∂κ) 2 μ := by
  have hs := (memLp_two_iff_integrable_sq_norm hp.1).mp hp
  have hslice : ∀ᵐ x ∂μ, MemLp (fun k => F (x,k)) 2 κ := by
    filter_upwards [hs.prod_right_ae] with x hx
    exact (memLp_two_iff_integrable_sq_norm (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx
  refine ⟨hslice.mono (fun x hx => hx.integrable (by norm_num)),?_⟩
  have hm := hF.integral_prod_right' (ν := κ)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply hs.integral_prod_left.mono' (hm.norm.pow 2).aestronglyMeasurable
  filter_upwards [hslice] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact cyclic_IdeleSphericalL2_mean_sq_bound κ hx

variable [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Classes] [BorelSpace Classes]
    (κ : Measure K) [IsProbabilityMeasure κ]

abbrev H := Lp ℂ 2 (volume : Measure ℝ)
abbrev HQ := Lp ℂ 2 (quotientHaar κ)

def logLift : H →ₗᵢ[ℂ] HQ κ :=
  Lp.compMeasurePreservingₗᵢ ℂ quotientLog (quotientLog_measurePreserving κ)

theorem logLift_ae (g : H) :
    ((logLift κ g : HQ κ) : Classes → ℂ) =ᵐ[quotientHaar κ] fun z => g (quotientLog z) :=
  Lp.coeFn_compMeasurePreserving g (quotientLog_measurePreserving κ)

def sector := (logLift κ).toLinearMap.range

instance complete_sector : CompleteSpace (sector κ) := by
  exact (logLift κ).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

def projection : HQ κ →L[ℂ] HQ κ := (sector κ).starProjection

def unitMean (F : Classes → ℂ) (x : ℝ) : ℂ :=
  ∫ k : K, F (quotientChart (Multiplicative.ofAdd x,k)) ∂κ

theorem unitMean_memLp (F : HQ κ) :
    (∀ᵐ x : ℝ, Integrable (fun k : K => F (quotientChart (Multiplicative.ofAdd x,k))) κ) ∧
      MemLp (unitMean κ F) 2 (volume : Measure ℝ) := by
  let p := MasulloRH.IdeleQuotient.realChart quotientChart
  have hchart : MeasurePreserving p ((volume : Measure ℝ).prod κ) (quotientHaar κ) :=
    quotientChart_measurePreserving κ
  exact fiber_mean_memLp κ ((Lp.stronglyMeasurable F).comp_measurable hchart.measurable)
    ((Lp.memLp F).comp_measurePreserving hchart)

private theorem cyclic_IdeleSphericalL2_inner_logLift (g : H) (F : HQ κ) :
    ⟪logLift κ g,F⟫_ℂ = ⟪g,((unitMean_memLp κ F).2.toLp (unitMean κ F))⟫_ℂ := by
  let J (z : Classes) := ⟪g (quotientLog z),F z⟫_ℂ
  have he : (fun z : Classes => ⟪(logLift κ g) z,F z⟫_ℂ) =ᵐ[quotientHaar κ] J := by
    filter_upwards [logLift_ae κ g] with z hz
    rw [hz]
  have hJ : Integrable J (quotientHaar κ) := (L2.integrable_inner (𝕜:=ℂ) (logLift κ g) F).congr he
  rw [L2.inner_def,integral_congr_ae he,integral_quotientHaar κ J hJ,L2.inner_def]
  have hx := (unitMean_memLp κ F).2.coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hx] with x hmean
  rw [hmean]
  change (∫ k : K, ⟪g (quotientLog ((QuotientGroup.mk' principal.range) (rep (Multiplicative.ofAdd x,k)))),
    F (quotientChart (Multiplicative.ofAdd x,k))⟫_ℂ ∂κ) = ⟪g x, unitMean κ F x⟫_ℂ
  simp only [quotientLog_mk_rep,unitMean,RCLike.inner_apply,integral_mul_const]
  rfl

theorem projection_as_lift (F : HQ κ) :
    projection κ F = logLift κ ((unitMean_memLp κ F).2.toLp (unitMean κ F)) := by
  let v : H := (unitMean_memLp κ F).2.toLp _
  apply Submodule.eq_starProjection_of_mem_orthogonal (K := sector κ) (v := logLift κ v) ⟨v,rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨g,rfl⟩
  change ⟪logLift κ g,F-logLift κ v⟫_ℂ=0
  rw [inner_sub_right,cyclic_IdeleSphericalL2_inner_logLift κ g F,(logLift κ).inner_map_map,sub_self]

theorem projection_ae_logMean (F : HQ κ) :
    ((projection κ F : HQ κ) : Classes → ℂ) =ᵐ[quotientHaar κ] fun z => unitMean κ F (quotientLog z) := by
  rw [projection_as_lift]
  exact (logLift_ae κ _).trans ((quotientLog_measurePreserving κ).quasiMeasurePreserving.ae_eq_comp
    (unitMean_memLp κ F).2.coeFn_toLp)

omit [MeasurableSpace Classes] [BorelSpace Classes] [IsProbabilityMeasure κ] in
theorem unitMean_eq_class_orbit [κ.IsMulLeftInvariant] (F : Classes → ℂ) (z : Classes) :
    unitMean κ F (quotientLog z) = ∫ k : K, F (z*quotientChart (1,k)) ∂κ := by
  obtain ⟨⟨x,u⟩,rfl⟩ := quotientChart.surjective z
  change (∫ k : K, F (quotientChart (Multiplicative.ofAdd
      (quotientLog ((QuotientGroup.mk' principal.range) (rep (x,u)))),k)) ∂κ) = _
  simp only [quotientLog_mk_rep]
  have he (k : K) : quotientChart (x,u) * quotientChart (1,k) = quotientChart (x,u*k) := by
    rw [←map_mul]
    simp
  simp_rw [he]
  exact (integral_mul_left_eq_self (fun k : K => F (quotientChart (x,k))) u).symm

/-- Orthogonal projection onto the closed subspace of functions of the log norm equals
Haar averaging along the finite-unit orbit, for every square-integrable class function. -/
theorem projection_ae_unit_average [κ.IsMulLeftInvariant] (F : HQ κ) :
    ((projection κ F : HQ κ) : Classes → ℂ) =ᵐ[quotientHaar κ]
      fun z => ∫ k : K, F (z*quotientChart (1,k)) ∂κ :=
  (projection_ae_logMean κ F).trans (ae_of_all _ (unitMean_eq_class_orbit κ F))

omit [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Classes] [BorelSpace Classes] in
private theorem cyclic_IdeleSphericalL2_orbit_coords (z : Classes) (k : K) :
    z*quotientChart (1,k) = quotientChart ((quotientChart.symm z).1,(quotientChart.symm z).2*k) := by
  obtain ⟨⟨x,u⟩,rfl⟩ := quotientChart.surjective z
  rw [quotientChart.symm_apply_apply,←map_mul]
  simp

theorem integrable_class_orbit_ae [κ.IsMulLeftInvariant] (F : HQ κ) :
    ∀ᵐ z ∂quotientHaar κ, Integrable (fun k : K => F (z*quotientChart (1,k))) κ := by
  have hz := (quotientLog_measurePreserving κ).quasiMeasurePreserving.ae (unitMean_memLp κ F).1
  filter_upwards [hz] with z h
  simp only [cyclic_IdeleSphericalL2_orbit_coords]
  exact (measurePreserving_mul_left κ (quotientChart.symm z).2).integrable_comp_of_integrable h

theorem mem_sector_iff_ae_fiber [κ.IsMulLeftInvariant] (F : HQ κ) :
    F ∈ sector κ ↔ ∀ᵐ z ∂quotientHaar κ, ∀ᵐ k ∂κ, F (z*quotientChart (1,k)) = F z := by
  constructor
  · rintro ⟨g,rfl⟩
    have hq := logLift_ae κ g
    have he : ∀ᵐ p : ℝ × K ∂volume.prod κ,
        logLift κ g (quotientChart (Multiplicative.ofAdd p.1,p.2)) = g p.1 := by
      have hh := (quotientChart_measurePreserving κ).quasiMeasurePreserving.ae_eq_comp hq
      filter_upwards [hh] with p hp
      change logLift κ g ((QuotientGroup.mk' principal.range) (rep (Multiplicative.ofAdd p.1,p.2))) = g p.1
      simp only [Function.comp_apply,quotientLog_mk_rep] at hp
      exact hp.trans (congrArg (fun t : ℝ => g t) (show (Multiplicative.ofAdd p.1).toAdd = p.1 from rfl))
    have hs : ∀ᵐ x : ℝ, ∀ᵐ k : K ∂κ, logLift κ g (quotientChart (Multiplicative.ofAdd x,k)) = g x :=
      Measure.ae_ae_of_ae_prod he
    have hz := (quotientLog_measurePreserving κ).quasiMeasurePreserving.ae hs
    filter_upwards [hq,hz] with z hz0 hz1
    have hk := (measurePreserving_mul_left κ (quotientChart.symm z).2).quasiMeasurePreserving.ae hz1
    filter_upwards [hk] with k h
    change logLift κ g (z*quotientChart (1,k)) = logLift κ g z
    rw [cyclic_IdeleSphericalL2_orbit_coords,hz0]
    exact h
  · intro hf
    apply Submodule.starProjection_eq_self_iff.mp
    apply Lp.ext
    filter_upwards [projection_ae_unit_average κ F,hf] with z hz hk
    exact hz.trans ((integral_congr_ae hk).trans (by simp))

end
end MasulloRH.IdeleSphericalL2

end StandaloneIdeleSphericalL2

section StandaloneIdelePublic

open MeasureTheory NumberField IsDedekindDomain Set
open MasulloRH.RationalFinite
open scoped Topology ENNReal SchwartzMap InnerProductSpace
namespace MasulloRH.RationalClass
noncomputable section

theorem norm_mk (x : I) : normHom (classOf x) = TateGlobal.ideleNorm ℚ x :=
  (IdeleCoordinates.ideleNorm_normalized x).symm

theorem norm_eq : normHom = IdeleCoordinates.quotientNorm := by
  apply MonoidHom.ext
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective principal.range z
  exact norm_mk x

theorem log_chart (h : Multiplicative ℝ × K) : logNorm (IdeleCoordinates.quotientChart h) = h.1.toAdd := by
  change Real.log (normHom (classOf (IdeleCoordinates.rep h))) = _
  rw [norm_mk,IdeleCoordinates.ideleNorm_rep,Real.log_exp]

theorem log_eq_coord : logNorm = IdeleCoordinates.quotientLog := by
  funext z
  obtain ⟨h,rfl⟩ := IdeleCoordinates.quotientChart.surjective z
  exact (log_chart h).trans (IdeleCoordinates.quotientLog_mk_rep h).symm

theorem finiteUnit_eq_chart (u : K) : finiteUnit u = IdeleCoordinates.quotientChart (1,u) := by
  apply congrArg classOf
  apply Units.ext
  apply Prod.ext
  · change 1 = (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) (Real.exp 0))
    simp only [Real.exp_zero,map_one]
  · rfl

theorem orbit_eq_descend (F : Ad → ℂ) : orbitTheta F = IdeleOrbit.descend F := by
  funext z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective principal.range z
  rfl

theorem spherical_eq [MeasurableSpace K] (κ : Measure K) (F : Ad → ℂ) :
    sphericalTheta κ F = IdeleOrbit.projected κ IdeleCoordinates.quotientChart F := by
  funext z
  simp only [sphericalTheta,IdeleOrbit.projected,orbit_eq_descend,finiteUnit_eq_chart]
  rfl

theorem image_public [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    {Φ : C → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0 = 0 ∧ (∫ a, F a ∂μ) = 0 ∧
        Φ = sphericalTheta κ F} =
    {Φ : C → ℂ | ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧
        ∀ z, Φ z = ∑' n : ℤ, g ((n:ℝ)*Real.exp (logNorm z))} := by
  simp only [spherical_eq,log_eq_coord]
  exact IdeleOrbit.image μ κ IdeleCoordinates.quotientChart (fun _ => rfl)

end
end MasulloRH.RationalClass

end StandaloneIdelePublic

section StandaloneIdeleFinal

open NumberField IsDedekindDomain MeasureTheory Set
open MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped Topology ENNReal SchwartzMap InnerProductSpace

theorem solution [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] [mC : MeasurableSpace C] [bC : BorelSpace C] :
    (∀ x : I, normHom (classOf x) = TateGlobal.ideleNorm ℚ x) ∧ CompactSpace normHom.ker ∧
    (∃ κ : Measure K, κ.IsHaarMeasure ∧ IsProbabilityMeasure κ) ∧
    ∃ e : Multiplicative ℝ × K ≃ₜ* C,
      (∀ s : Multiplicative ℝ, ∀ u : K, ∃ x : I,
        (x:Ad) = ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
          (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) (Real.exp s.toAdd)), (u.val:A)) ∧
        classOf x = e (s,u) ∧ logNorm (classOf x) = s.toAdd) ∧
      (∀ u : K, finiteUnit u = e (1,u)) ∧
      ∀ (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ],
        let h := fun v : ℝ × K => e (Multiplicative.ofAdd v.1,v.2)
        ∃ ν : Measure C, ν.IsHaarMeasure ∧
          MeasurePreserving h ((volume : Measure ℝ).prod κ) ν ∧
          MeasurePreserving logNorm ν (volume : Measure ℝ) ∧
          (∀ a b : ℝ, ν (h '' (Icc a b ×ˢ univ)) = ENNReal.ofReal (b-a)) ∧
          (∀ F : C → ℂ, Integrable F ν → (∫ z, F z ∂ν) =
            ∫ x : ℝ, ∫ u : K, F (e (Multiplicative.ofAdd x,u)) ∂κ) ∧
          {Φ : C → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0=0 ∧ (∫ a, F a ∂μ)=0 ∧
              Φ = sphericalTheta κ F} =
            {Φ : C → ℂ | ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧
              ∀ z, Φ z = ∑' n : ℤ, g ((n:ℝ)*Real.exp (logNorm z))} ∧
          ∃ J : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 ν,
            (∀ g, (J g : C → ℂ) =ᵐ[ν] fun z => g (logNorm z)) ∧
            IsClosed (J.toLinearMap.range : Set (Lp ℂ 2 ν)) ∧
            (∀ F : Lp ℂ 2 ν, F ∈ J.toLinearMap.range ↔
               ∀ᵐ z ∂ν, ∀ᵐ u ∂κ, F (z*finiteUnit u) = F z) ∧
            ∃ P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ F : Lp ℂ 2 ν,
              P F ∈ J.toLinearMap.range ∧ F-P F ∈ J.toLinearMap.rangeᗮ ∧
              (∀ᵐ z ∂ν, Integrable (fun u : K => F (z*finiteUnit u)) κ) ∧
              (P F : C → ℂ) =ᵐ[ν] fun z => ∫ u : K, F (z*finiteUnit u) ∂κ := by
  let : MeasurableSpace MasulloRH.IdeleCoordinates.Classes := mC
  let : BorelSpace MasulloRH.IdeleCoordinates.Classes := bC
  have hcompact : CompactSpace normHom.ker := by
    rw [MasulloRH.RationalClass.norm_eq]
    exact MasulloRH.IdeleCoordinates.compact_quotientNorm_ker
  refine ⟨norm_mk,hcompact,MasulloRH.IdeleCoordinates.exists_unit_haar_probability,
    MasulloRH.IdeleCoordinates.quotientChart,?_,finiteUnit_eq_chart,?_⟩
  · intro s u
    exact ⟨_,MasulloRH.IdeleCoordinates.rep_val (s,u),rfl,log_chart (s,u)⟩
  · intro κ _ _ h
    refine ⟨MasulloRH.IdeleCoordinates.quotientHaar κ,MasulloRH.IdeleCoordinates.quotientHaar_isHaarMeasure κ,
      MasulloRH.IdeleCoordinates.quotientChart_measurePreserving κ,?_,
      MasulloRH.IdeleCoordinates.quotientHaar_slab κ,MasulloRH.IdeleCoordinates.integral_quotientHaar κ,
      image_public μ κ,MasulloRH.IdeleSphericalL2.logLift κ,?_,?_,?_,MasulloRH.IdeleSphericalL2.projection κ,?_⟩
    · rw [log_eq_coord]
      exact MasulloRH.IdeleCoordinates.quotientLog_measurePreserving κ
    · rw [log_eq_coord]
      exact MasulloRH.IdeleSphericalL2.logLift_ae κ
    · exact (MasulloRH.IdeleSphericalL2.logLift κ).isometry.isClosedEmbedding.isClosed_range
    · simp only [finiteUnit_eq_chart]
      exact MasulloRH.IdeleSphericalL2.mem_sector_iff_ae_fiber κ
    · intro F
      simp only [finiteUnit_eq_chart]
      exact ⟨(MasulloRH.IdeleSphericalL2.sector κ).starProjection_apply_mem F,
        Submodule.sub_starProjection_mem_orthogonal (K:=MasulloRH.IdeleSphericalL2.sector κ) F,
        MasulloRH.IdeleSphericalL2.integrable_class_orbit_ae κ F,
        MasulloRH.IdeleSphericalL2.projection_ae_unit_average κ F⟩

end StandaloneIdeleFinal
