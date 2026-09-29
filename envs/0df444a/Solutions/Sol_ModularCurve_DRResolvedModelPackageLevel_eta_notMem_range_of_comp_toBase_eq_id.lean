-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.eta_notMem_range_of_comp_toBase_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e769d13b-f2dc-56d1-af27-e76a5acb6b69

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

universe u

namespace E5W2aEta

section Generic

variable {X : Scheme.{u}}

private theorem map_germ_ideal_eq_of_le (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) (x : X)
    (hxU : x ∈ (U : X.Opens)) :
    (I.ideal V).map (X.presheaf.germ (V : X.Opens) x (h hxU)).hom =
      (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hxU).hom := by
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  exact congrArg (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal V)) (X.presheaf.germ_res (homOfLE h) x hxU).symm

private theorem map_germ_ideal_eq (I : X.IdealSheafData) {U V : X.affineOpens} (x : X)
    (hxU : x ∈ (U : X.Opens)) (hxV : x ∈ (V : X.Opens)) :
    (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hxU).hom =
      (I.ideal V).map (X.presheaf.germ (V : X.Opens) x hxV).hom := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have hWU : X.affineBasicOpen f ≤ U := X.basicOpen_le f
  have hWV : (X.affineBasicOpen f : X.Opens) ≤ V := hfg.trans_le (X.basicOpen_le g)
  rw [map_germ_ideal_eq_of_le I hWU x hxf, map_germ_ideal_eq_of_le I (U := X.affineBasicOpen f) (V := V) hWV x hxf]

private theorem not_mem_support_of_map_germ_eq_top (I : X.IdealSheafData) (x : X) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens)) (h : (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom = ⊤) :
    x ∉ I.support := by
  intro hs
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, Scheme.mem_zeroLocus_iff] at hs
  have hle : (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hs f hf ((X.mem_basicOpen f x hx).mpr hu)
  rw [h, top_le_iff] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top hle

private theorem germ_mem_nonZeroDivisors (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) :
    (X.presheaf.germ (U : X.Opens) x hx).hom g ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  letI := X.presheaf.algebra_section_stalk (U := (U : X.Opens)) ⟨x, hx⟩
  haveI := U.2.isLocalization_stalk ⟨x, hx⟩
  have h := IsLocalization.nonZeroDivisors_le_comap ((U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    (X.presheaf.stalk x) hg
  exact h

private theorem one_le_ringKrullDim_of_not_isNilpotent {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hn : ¬ IsNilpotent x) : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h0 : (IsLocalRing.maximalIdeal R).height ≠ 0 := by
    intro h0
    rw [Ideal.height_eq_zero_iff] at h0
    apply hn
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJm : J ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hJ.ne_top
    exact h0.2 ⟨hJ, bot_le⟩ hJm hx
  exact_mod_cast ENat.one_le_iff_ne_zero.mpr h0

private theorem ringKrullDim_le_one_of_maximalIdeal_eq_span {B : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (g : B) (h : IsLocalRing.maximalIdeal B = Ideal.span {g}) : ringKrullDim B ≤ 1 := by
  haveI : (IsLocalRing.maximalIdeal B).IsPrincipal := ⟨⟨g, h⟩⟩
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing (IsLocalRing.maximalIdeal B)
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast h1

private theorem preimage_basicOpen_natCast {O : Type u} [CommRing O] {Y : Scheme.{u}} (b : Y ⟶ Spec (CommRingCat.of O)) (p : ℕ) :
    b ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) = Y.basicOpen ((p : ℕ) : Γ(Y, ⊤)) := by
  have e : (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) =
      (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((p : ℕ) : O)) :=
    (basicOpen_eq_of_affine _).symm
  rw [e, Scheme.preimage_basicOpen_top, map_natCast, map_natCast]

private theorem natCast_mem_maximalIdeal_stalk {O : Type u} [CommRing O] {Y : Scheme.{u}} (b : Y ⟶ Spec (CommRingCat.of O))
    (p : ℕ) (y : Y) (hy : y ∉ b ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ((p : ℕ) : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hy
  rw [preimage_basicOpen_natCast, Y.mem_basicOpen ((p : ℕ) : Γ(Y, ⊤)) y (Set.mem_univ y)]
  rwa [map_natCast]

end Generic

section Pkg

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀} {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ} (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)

private theorem chainPos_ne_succ {node : Type} (width : node → ℕ) (n : node) (d : ℕ) (hd : d < width n) :
    DRResolvedModelPackageLevel.chainPos width n d ≠ DRResolvedModelPackageLevel.chainPos width n (d + 1) := by
  unfold DRResolvedModelPackageLevel.chainPos
  by_cases h0 : d = 0
  · subst h0
    simp only [↓reduceDIte, Nat.zero_add, one_ne_zero]
    split_ifs with h <;> simp
  · simp only [h0, ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    by_cases h1 : d + 1 < width n
    · simp only [hd, ↓reduceDIte, h1, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg (fun q : Σ n, Fin (width n - 1) => (q.2 : ℕ)) h
      simp at this
      omega
    · simp [hd, h1]

private theorem isInvertible_prod : (∏ v, R.comp v).IsInvertible := by
  refine Finset.prod_induction _ (fun J : R.Y.IdealSheafData => J.IsInvertible)
    (fun _ _ h h' => h.mul h') ?_ (fun v _ => R.comp_isInvertible v)
  rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top

private theorem natCast_mem_nonZeroDivisors_stalk (y : R.Y) :
    ((p : ℕ) : R.Y.presheaf.stalk y) ∈ nonZeroDivisors (R.Y.presheaf.stalk y) := by
  obtain ⟨U, f, hyf, g, hg, hI⟩ := isInvertible_prod R y
  have hgp : g ∈ Ideal.span {((p : ℕ) : Γ(R.Y, R.Y.affineBasicOpen f))} := by
    rw [← R.comp_prod (R.Y.affineBasicOpen f), hI]; exact Ideal.mem_span_singleton_self g
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hgp
  have hg' : a * ((p : ℕ) : Γ(R.Y, R.Y.affineBasicOpen f)) ∈ nonZeroDivisors _ := by rwa [ha]
  have hpU : ((p : ℕ) : Γ(R.Y, R.Y.affineBasicOpen f)) ∈ nonZeroDivisors _ := (mul_mem_nonZeroDivisors.mp hg').2
  have := germ_mem_nonZeroDivisors (R.Y.affineBasicOpen f) y hyf _ hpU
  rwa [map_natCast] at this

private theorem false_of_generic_data [IsLocalRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (σ : Spec (CommRingCat.of O) ⟶ R.Y) (hσ : σ ≫ R.toBase = 𝟙 _) (c : X0MqComponents R.width)
    (t : Spec (CommRingCat.of O)) (y0 : R.Y) (hy : σ.base t = y0)
    (U : R.Y.affineOpens) (hU : y0 ∈ (U : R.Y.Opens))
    (hmax : Ideal.map (R.Y.presheaf.germ (U : R.Y.Opens) y0 hU).hom ((R.comp c).ideal U) =
        IsLocalRing.maximalIdeal (R.Y.presheaf.stalk y0))
    (hunit : ∀ w, w ≠ c → Ideal.map (R.Y.presheaf.germ (U : R.Y.Opens) y0 hU).hom ((R.comp w).ideal U) = ⊤)
    (hfib : y0 ∉ R.toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) : False := by
  classical
  subst hy

  have htb : R.toBase.base (σ.base t) = t := by
    have h := congrArg (fun f : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O) => f.base t) hσ
    simpa using h
  have hp : ((p : ℕ) : O) ∈ t.asIdeal := by
    by_contra h
    apply hfib
    show R.toBase.base (σ.base t) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
    rw [htb]
    exact h
  obtain rfl : t = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le t.2.ne_top ?_).symm
    rw [hϖ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hp
  haveI : IsNoetherianRing (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) := inferInstance

  obtain ⟨U1, f1, hxf1, g1, -, hI1⟩ := R.comp_isInvertible c (σ.base (IsLocalRing.closedPoint O))
  have hmax' : IsLocalRing.maximalIdeal (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) =
      Ideal.span {(R.Y.presheaf.germ (R.Y.affineBasicOpen f1) (σ.base (IsLocalRing.closedPoint O)) hxf1).hom g1} := by
    rw [← hmax, map_germ_ideal_eq (R.comp c) (σ.base (IsLocalRing.closedPoint O)) hU hxf1 (V := R.Y.affineBasicOpen f1),
      hI1, Ideal.map_span, Set.image_singleton]
  have hdimB : ringKrullDim (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) ≤ 1 :=
    ringKrullDim_le_one_of_maximalIdeal_eq_span _ hmax'

  haveI : IsClosedImmersion (σ ≫ R.toBase) := by rw [hσ]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ R.toBase
  have hone : ∀ w, w ≠ c → σ.base (IsLocalRing.closedPoint O) ∉ (R.comp w).support := fun w hw =>
    not_mem_support_of_map_germ_eq_top (R.comp w) (σ.base (IsLocalRing.closedPoint O)) U hU (hunit w hw)
  have hsm : σ.base (IsLocalRing.closedPoint O) ∈ R.smoothOffEdges := by
    apply R.mem_smoothOffEdges
    intro n d h
    have hm := R.edgePt_mem n d
    rw [← h] at hm
    rcases eq_or_ne (DRResolvedModelPackageLevel.chainPos R.width n d) c with h1 | h1
    · exact hone _ (fun h2 => chainPos_ne_succ R.width n d d.isLt (h1.trans h2.symm)) hm.2
    · exact hone _ h1 hm.1
  have hker : σ.ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens R.toBase R.smoothOffEdges σ hσ hsm
  obtain ⟨U2, f2, hxf2, g2, hg2, hI2⟩ := hker (σ.base (IsLocalRing.closedPoint O))
  have hg2B : (R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2).hom g2 ∈
      nonZeroDivisors (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) := germ_mem_nonZeroDivisors _ _ hxf2 g2 hg2
  have hg2ker : (σ.app (R.Y.affineBasicOpen f2)) g2 = 0 := by
    have h := σ.ideal_ker_le (R.Y.affineBasicOpen f2) (hI2 ▸ Ideal.mem_span_singleton_self g2)
    exact h
  have hzero : (σ.stalkMap (IsLocalRing.closedPoint O)).hom
      ((R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2).hom g2) = 0 := by
    show (σ.stalkMap (IsLocalRing.closedPoint O))
      ((R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2) g2) = 0
    rw [Scheme.Hom.germ_stalkMap_apply, hg2ker, map_zero]
  have hg2m : (R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2).hom g2 ∈
      IsLocalRing.maximalIdeal (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := hu.map (σ.stalkMap (IsLocalRing.closedPoint O)).hom
    rw [hzero] at h
    exact not_isUnit_zero h
  have hle : Ideal.span {(R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2).hom g2} ≤
      RingHom.ker (σ.stalkMap (IsLocalRing.closedPoint O)).hom := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact hzero
  have hsurj : Function.Surjective
      (Ideal.Quotient.lift _ (σ.stalkMap (IsLocalRing.closedPoint O)).hom (fun a ha => hle ha)) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (σ.stalkMap_surjective (IsLocalRing.closedPoint O))
  have hdimO := ringKrullDim_le_of_surjective _ hsurj
  have hsucc := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hg2B hg2m

  let ψ := (R.toBase.stalkMap (σ.base (IsLocalRing.closedPoint O))).hom
  have hpB := natCast_mem_nonZeroDivisors_stalk R (σ.base (IsLocalRing.closedPoint O))
  have hpm : ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk (R.toBase.base (σ.base (IsLocalRing.closedPoint O)))) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := hu.map ψ
    rw [map_natCast] at h
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp
      (natCast_mem_maximalIdeal_stalk R.toBase p (σ.base (IsLocalRing.closedPoint O)) hfib)) h
  have hpn : ¬ IsNilpotent ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk (R.toBase.base (σ.base (IsLocalRing.closedPoint O)))) := by
    rintro ⟨n, hn⟩
    have h := congrArg ψ hn
    rw [map_pow, map_natCast, map_zero] at h
    have h0 : (0 : R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) ∈ nonZeroDivisors _ := h ▸ pow_mem hpB n
    exact zero_notMem_nonZeroDivisors h0
  have h1O := one_le_ringKrullDim_of_not_isNilpotent hpm hpn
  have hOO : ringKrullDim ((Spec (CommRingCat.of O)).presheaf.stalk (R.toBase.base (σ.base (IsLocalRing.closedPoint O)))) =
      ringKrullDim ((Spec (CommRingCat.of O)).presheaf.stalk (IsLocalRing.closedPoint O)) :=
    ringKrullDim_eq_of_ringEquiv
      ((Spec (CommRingCat.of O)).presheaf.stalkCongr (.of_eq htb)).commRingCatIsoToRingEquiv

  have key : (1 : WithBot ℕ∞) + 1 ≤ 1 :=
    calc (1 : WithBot ℕ∞) + 1 ≤ ringKrullDim ((Spec (CommRingCat.of O)).presheaf.stalk (IsLocalRing.closedPoint O)) + 1 := by
          rw [← hOO]; exact add_le_add h1O le_rfl
      _ ≤ ringKrullDim (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O)) ⧸
            Ideal.span {(R.Y.presheaf.germ (R.Y.affineBasicOpen f2) (σ.base (IsLocalRing.closedPoint O)) hxf2).hom g2}) + 1 :=
          add_le_add hdimO le_rfl
      _ = ringKrullDim (R.Y.presheaf.stalk (σ.base (IsLocalRing.closedPoint O))) := hsucc
      _ ≤ 1 := hdimB
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at key
  exact absurd key (by norm_num)

end Pkg

end E5W2aEta

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (σ : Spec (CommRingCat.of O) ⟶ R.Y) (hσ : σ ≫ R.toBase = 𝟙 _) (c : X0MqComponents R.width) :
    R.η c ∉ Set.range σ.base := by
  rintro ⟨t, ht⟩
  obtain ⟨U, hU, hmax, hunit⟩ := R.η_stalk c
  exact E5W2aEta.false_of_generic_data R hϖ σ hσ c t (R.η c) ht U hU hmax hunit (R.η_not_mem c)

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_eta_notMem_range_of_comp_toBase_eq_id (solution)
