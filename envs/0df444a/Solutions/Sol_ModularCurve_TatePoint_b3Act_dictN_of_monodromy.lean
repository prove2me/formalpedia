-- Prove2me | solution 1 for ModularCurve.TatePoint.b3Act_dictN_of_monodromy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4b381b7c-062b-569d-a82b-385836cfa01c

import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_ModularCurve_SpecialisationBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TatePoint_b3Act_dictN_of_monodromy

open scoped Classical

set_option autoImplicit false

noncomputable section

namespace S15CycSubN

open ModularCurve ModularCurve.TatePoint ModularCurve.B3 WeierstrassCurve

attribute [local instance] ModularCurve.TatePoint.isAlgClosed_H ModularCurve.TatePoint.charZero_H

theorem veluGx_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
    (x y : R) : (W.map φ).veluGx (φ x) (φ y) = φ (W.veluGx x y) := by
  simp only [veluGx, map_a₁, map_a₂, map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem veluGy_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
    (x y : R) : (W.map φ).veluGy (φ x) (φ y) = φ (W.veluGy x y) := by
  simp only [veluGy, map_a₁, map_a₃, map_neg, map_add, map_mul, map_ofNat]

theorem veluQuotientOfSums_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (φ : R →+* S) (t w : R) :
    (W.veluQuotientOfSums t w).map φ = (W.map φ).veluQuotientOfSums (φ t) (φ w) := by
  ext
  · simp only [map_a₁, veluQuotientOfSums_a₁]
  · simp only [map_a₂, veluQuotientOfSums_a₂]
  · simp only [map_a₃, veluQuotientOfSums_a₃]
  · simp only [map_a₄, veluQuotientOfSums_a₄, map_sub, map_mul, map_ofNat]
  · simp only [map_a₆, veluQuotientOfSums_a₆, map_b₂, map_sub, map_mul, map_ofNat]

theorem j_congr {V V' : WeierstrassCurve H} (h : V = V') (hV : V.IsElliptic) (hV' : V'.IsElliptic) :
    @WeierstrassCurve.j H _ V hV = @WeierstrassCurve.j H _ V' hV' := by
  subst h; rfl

section Transport

variable (j₀ : Qbar) (m : HahnSeries.monodromy Qbar)

theorem coordsOrZero_nearTransport (P : (nearCurve j₀).toAffine.Point) :
    (nearTransport j₀ m P).coordsOrZero =
      Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H) P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · have h0 : nearTransport j₀ m (Affine.Point.zero) = Affine.Point.zero := map_zero (nearTransport j₀ m)
    rw [h0, Affine.Point.coordsOrZero_zero]
    ext <;> simp
  · rw [nearTransport_some]
    rfl

theorem oddOrderSummingSet_nearTransport (g : (nearCurve j₀).toAffine.Point) (n : ℕ) :
    (nearCurve j₀).oddOrderSummingSet (nearTransport j₀ m g) n =
      ((nearCurve j₀).oddOrderSummingSet g n).image
        (Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H)) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  rw [Function.comp_apply, ← coordsOrZero_nearTransport, map_nsmul]

theorem addOrderOf_nearTransport (P : (nearCurve j₀).toAffine.Point) :
    addOrderOf (nearTransport j₀ m P) = addOrderOf P := by
  rw [addOrderOf_eq_addOrderOf_iff]
  intro n
  rw [← map_nsmul, ← map_zero (nearTransport j₀ m)]
  exact (nearTransport j₀ m).injective.eq_iff

theorem fullKernelQuotient_nearTransport (Q : (nearCurve j₀).toAffine.Point) (N : ℕ) :
    (nearCurve j₀).fullKernelQuotient (nearTransport j₀ m Q) N =
      ((nearCurve j₀).fullKernelQuotient Q N).map ((m : H ≃ₐ[Qbar] H) : H →+* H) := by
  have hE := nearCurve_map_of_mem_monodromy j₀ m.2
  have hinj : Function.Injective
      (Prod.map ((m : H ≃ₐ[Qbar] H) : H →+* H) ((m : H ≃ₐ[Qbar] H) : H →+* H)) :=
    Prod.map_injective.mpr ⟨(m : H ≃ₐ[Qbar] H).injective, (m : H ≃ₐ[Qbar] H).injective⟩
  have hgx : ∀ x y : H, (nearCurve j₀).veluGx ((m : H ≃ₐ[Qbar] H) x) ((m : H ≃ₐ[Qbar] H) y) =
      (m : H ≃ₐ[Qbar] H) ((nearCurve j₀).veluGx x y) := fun x y => by
    have h := veluGx_map (nearCurve j₀) ((m : H ≃ₐ[Qbar] H) : H →+* H) x y
    rw [hE] at h
    exact h
  have hgy : ∀ x y : H, (nearCurve j₀).veluGy ((m : H ≃ₐ[Qbar] H) x) ((m : H ≃ₐ[Qbar] H) y) =
      (m : H ≃ₐ[Qbar] H) ((nearCurve j₀).veluGy x y) := fun x y => by
    have h := veluGy_map (nearCurve j₀) ((m : H ≃ₐ[Qbar] H) : H →+* H) x y
    rw [hE] at h
    exact h
  have hq := veluQuotientOfSums_map (nearCurve j₀) ((m : H ≃ₐ[Qbar] H) : H →+* H)
  rw [hE] at hq
  rw [fullKernelQuotient, fullKernelQuotient, hq, oddOrderSummingSet_nearTransport,
    Finset.sum_image (hinj.injOn.mono (Set.subset_univ _)),
    Finset.sum_image (hinj.injOn.mono (Set.subset_univ _)), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun P _ => ?_
    obtain ⟨x, y⟩ := P
    exact hgx x y
  · refine Finset.sum_congr rfl fun P _ => ?_
    obtain ⟨x, y⟩ := P
    show (m : H ≃ₐ[Qbar] H) x * (nearCurve j₀).veluGx ((m : H ≃ₐ[Qbar] H) x) ((m : H ≃ₐ[Qbar] H) y) -
        (m : H ≃ₐ[Qbar] H) y * (nearCurve j₀).veluGy ((m : H ≃ₐ[Qbar] H) x) ((m : H ≃ₐ[Qbar] H) y) =
      (m : H ≃ₐ[Qbar] H) (x * (nearCurve j₀).veluGx x y - y * (nearCurve j₀).veluGy x y)
    rw [map_sub, map_mul, map_mul, hgx, hgy]

theorem j_fullKernelQuotient_nearTransport (Q : (nearCurve j₀).toAffine.Point) (N : ℕ)
    (hQ : ((nearCurve j₀).fullKernelQuotient Q N).IsElliptic)
    (hQ' : ((nearCurve j₀).fullKernelQuotient (nearTransport j₀ m Q) N).IsElliptic) :
    @WeierstrassCurve.j H _ _ hQ' = (m : H ≃ₐ[Qbar] H) (@WeierstrassCurve.j H _ _ hQ) := by
  haveI := hQ
  rw [j_congr (fullKernelQuotient_nearTransport j₀ m Q N) hQ' inferInstance]
  exact WeierstrassCurve.map_j _ _

end Transport

theorem b3Act_dictN_of_monodromy (N : ℕ) [NeZero N] (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N) :
    ∀ (data : ModularPolynomialData N) (m : HahnSeries.monodromy Qbar)
      (r r' : RootsAt data (nearCurve j₀).j),
      r'.1 = (↑m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 =
          (dictN N data j₀ hW1 hW2 hW3 r').1 := by
  intro data m r r' hr
  set G : CycSubH (nearCurve j₀) N := dictN N data j₀ hW1 hW2 hW3 r with hGdef
  set G'' : CycSubH (nearCurve j₀) N := dictN N data j₀ hW1 hW2 hW3 r' with hG''def

  have hA1 : r = cycSubRootN (nearCurve j₀) hW1 hW3 data G :=
    (dictN_apply_eq_iff N data j₀ hW1 hW2 hW3 r G).mp hGdef.symm
  have hA2 : r' = cycSubRootN (nearCurve j₀) hW1 hW3 data G'' :=
    (dictN_apply_eq_iff N data j₀ hW1 hW2 hW3 r' G'').mp hG''def.symm

  have hordτg : addOrderOf (nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) = N := by
    rw [addOrderOf_nearTransport]; exact addOrderOf_cycSubGen _ G

  have hQel : ((nearCurve j₀).fullKernelQuotient (cycSubGen (nearCurve j₀) G) N).IsElliptic :=
    isElliptic_fullKernelQuotient_cycSubGen (nearCurve j₀) hW3 G
  have hΔ' : ((nearCurve j₀).fullKernelQuotient
      (nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) N).Δ ≠ 0 :=
    hW3 two_ne_zero (nearCurve j₀) _ hordτg
  have hQel' : ((nearCurve j₀).fullKernelQuotient
      (nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) N).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  have hB := j_fullKernelQuotient_nearTransport j₀ m (cycSubGen (nearCurve j₀) G) N hQel hQel'

  have hjj : (cycSubRootN (nearCurve j₀) hW1 hW3 data G'').1 = @WeierstrassCurve.j H _ _ hQel' := by
    calc (cycSubRootN (nearCurve j₀) hW1 hW3 data G'').1
        = r'.1 := by rw [← hA2]
      _ = (m : H ≃ₐ[Qbar] H) r.1 := hr
      _ = (m : H ≃ₐ[Qbar] H) (cycSubRootN (nearCurve j₀) hW1 hW3 data G).1 := by rw [← hA1]
      _ = (m : H ≃ₐ[Qbar] H) (@WeierstrassCurve.j H _ _ hQel) := rfl
      _ = @WeierstrassCurve.j H _ _ hQel' := hB.symm

  have hzm : AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G'') =
      AddSubgroup.zmultiples (nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) :=
    hW2 (nearCurve j₀) (transcendental_rat_of_transcendental_qbar (nearCurve_j_transcendental j₀))
      (cycSubGen (nearCurve j₀) G'') (nearTransport j₀ m (cycSubGen (nearCurve j₀) G))
      (addOrderOf_cycSubGen _ G'') hordτg
      (isElliptic_fullKernelQuotient_cycSubGen (nearCurve j₀) hW3 G'').isUnit.ne_zero hΔ' hjj

  calc B3.b3Act j₀ m G.1
      = B3.b3Act j₀ m (AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G)) := by
        rw [← coe_eq_zmultiples_cycSubGen]
    _ = AddSubgroup.zmultiples (nearTransport j₀ m (cycSubGen (nearCurve j₀) G)) :=
        b3Act_zmultiples j₀ m (cycSubGen (nearCurve j₀) G)
    _ = AddSubgroup.zmultiples (cycSubGen (nearCurve j₀) G'') := hzm.symm
    _ = G''.1 := (coe_eq_zmultiples_cycSubGen (nearCurve j₀) G'').symm

end S15CycSubN

open ModularCurve ModularCurve.TatePoint in

theorem solution (N : ℕ) [NeZero N] (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N) :
    ∀ (data : ModularPolynomialData N) (m : HahnSeries.monodromy Qbar)
      (r r' : RootsAt data (nearCurve j₀).j),
      r'.1 = (↑m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 =
          (dictN N data j₀ hW1 hW2 hW3 r').1 :=
  S15CycSubN.b3Act_dictN_of_monodromy N j₀ hW1 hW2 hW3

end

end S_ModularCurve_TatePoint_b3Act_dictN_of_monodromy
end P2MW
export P2MW.S_ModularCurve_TatePoint_b3Act_dictN_of_monodromy (solution)
