-- Prove2me | solution 1 for GlobalTheory.HalfPairing.exists_adjoint_halves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:20.128603+00:00
-- url     : https://prove2.me/submissions/a33019b3-1a0c-44f0-b40f-4b6bf7af973d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint
import Theorems.Thm_GlobalTheory_HalfPairing_exists_adjoint
import Theorems.Thm_GlobalTheory_HalfPairing_cHalf_spec
import Theorems.Thm_GlobalTheory_HalfPairing_bar_mem
import Theorems.Thm_GlobalTheory_HalfPairing_ef_swap
import Theorems.Thm_GlobalTheory_HalfPairing_dvd_of_mem
import Theorems.Thm_GlobalTheory_HalfPairing_qRep_mk
import Theorems.Thm_GlobalTheory_LevelPairing_bar_bar
import Theorems.Thm_GlobalTheory_LevelPairing_exists_eq_smul_of_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
namespace GlobalTheory.HalfPairing
theorem _root_.solution (N : ℕ) (hN : N ≠ 0) (I : Ideal (𝓞 E))
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (KJ KI : Submodule (𝓞 E) Dw.La)
    (hKJ : KJ = I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤) (hKI : KI = I • ⊤) :
    ∃ adj : ((Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)) → ((Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)),
      (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : (Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)) (kst : (Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)),
        (∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H I • v) -
          Dw.EF u (cHalf H I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by
  obtain ⟨hc, hc1⟩ := cHalf_spec I hI
  set c := cHalf H I with hcdef
  have hmul : ∀ a ∈ I, a * c ∈ Ideal.span {(N : 𝓞 E)} := fun a ha => hp ▸ Ideal.mul_mem_mul ha hc
  have hright : ∀ x, ∀ y ∈ KI, (N : ℤ) ∣ Dw.EF x (c • y) := by
    intro x y hy
    rw [hKI] at hy
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact dvd_of_mem _ _ _ (hmul a ha)
    · rw [smul_add, map_add]; exact dvd_add hu hv
  have hleft : ∀ x ∈ KJ, ∀ y, (N : ℤ) ∣ Dw.EF x (c • y) := by
    intro x hx y
    rw [hKJ] at hx
    refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [Dw.adj, ← mul_smul]; exact dvd_of_mem _ _ _ (hmul _ (bar_mem ha))
    · rw [map_add, LinearMap.add_apply]; exact dvd_add hu hv
  let B : (Dw.La ⧸ KJ) → (Dw.La ⧸ KI) → ZMod N := fun p q => ((Dw.EF (qRep p) (c • qRep q) : ℤ) : ZMod N)
  have hB : ∀ u v, B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ((Dw.EF u (c • v) : ℤ) : ZMod N) := by
    intro u v
    rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 := (Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk u : Dw.La ⧸ KJ))
    have h2 := (Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk v : Dw.La ⧸ KI))
    have h3 := dvd_add (hleft _ h1 (qRep (Submodule.Quotient.mk v : Dw.La ⧸ KI))) (hright u _ h2)
    rwa [map_sub, LinearMap.sub_apply, smul_sub, map_sub, sub_add_sub_cancel] at h3
  have haddr : ∀ u v w, B u (v + w) = B u v + B u w := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, smul_add, map_add, Int.cast_add]
  have haddl : ∀ u u' v, B (u + u') v = B u v + B u' v := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, map_add, LinearMap.add_apply, Int.cast_add]
  have hbal : ∀ (a : 𝓞 E) u v, B u (a • v) = B (H.bar a • u) v := by
    intro a u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hB, hB, Dw.adj, LevelPairing.bar_bar,
      smul_comm]
  have hNI : (N : 𝓞 E) ∈ I := by
    have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have hnd : ∀ v w, (∀ u, B u v = B u w) → v = w := by
    intro v w h
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [eq_comm, Submodule.Quotient.eq, hKI]
    obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (c • (w - v)) N hN (fun y => by
      have := h (Submodule.Quotient.mk y)
      rw [hB, hB, ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      rw [ef_swap, dvd_neg, smul_sub, map_sub]
      exact this)
    have : w - v = (N : 𝓞 E) • z - (c - 1) • (w - v) := by
      rw [sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
    rw [this]
    exact sub_mem (Submodule.smul_mem_smul hNI trivial) (Submodule.smul_mem_smul hc1 trivial)
  have hrep : ∀ (g : (Dw.La ⧸ KJ) →ₗ[𝓞 E] (Dw.La ⧸ KJ)) (v : Dw.La ⧸ KI), ∃ w, ∀ u, B (g u) v = B u w := by
    intro g v
    haveI := Dw.proj
    haveI : Module.Projective ℤ Dw.La := by
      haveI := Dw.fin
      obtain ⟨m, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) Dw.La
      exact Module.Projective.of_split (s.restrictScalars ℤ) (p.restrictScalars ℤ)
        (LinearMap.ext fun x => LinearMap.congr_fun hps x)
    let f : Dw.La →+ ZMod N := AddMonoidHom.mk' (fun u => B (g (Submodule.Quotient.mk u)) v) (fun u u' => by
      simp only [Submodule.Quotient.mk_add, map_add, haddl])
    obtain ⟨F, hF⟩ := Module.projective_lifting_property (Int.castAddHom (ZMod N)).toIntLinearMap f.toIntLinearMap
      (ZMod.intCast_surjective)
    obtain ⟨w, hw⟩ := Dw.unimod.2 F
    have hF' : ∀ u, ((Dw.EF w u : ℤ) : ZMod N) = f u := fun u => by
      rw [hw]; exact LinearMap.congr_fun hF u
    refine ⟨Submodule.Quotient.mk (-w), fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : f (H.bar (c - 1) • u) = 0 := by
      have : (Submodule.Quotient.mk (H.bar (c - 1) • u) : Dw.La ⧸ KJ) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero, hKJ]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1) trivial
      change B (g (Submodule.Quotient.mk _)) v = 0
      rw [this, map_zero]
      have := haddl 0 0 v
      rw [add_zero] at this
      exact left_eq_add.1 this
    change f u = _
    have h1 : Dw.EF u (c • -w) = Dw.EF w (H.bar (c - 1) • u) + Dw.EF w u := by
      rw [← Dw.adj, ef_swap, sub_smul, one_smul, smul_neg, map_neg, map_sub]
      simp
    rw [hB, h1, Int.cast_add, hF', hF', h0, zero_add]
  obtain ⟨adj, h1, h2⟩ := exists_adjoint (fun a => H.bar a) B haddr hbal hnd hrep
  refine ⟨adj, h1, fun k g => ?_⟩
  rw [← h2]
  have key : ∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (g (Submodule.Quotient.mk u))) (c • v) -
      Dw.EF u (c • qRep (k (Submodule.Quotient.mk v)))) ↔
      B (g (Submodule.Quotient.mk u)) (Submodule.Quotient.mk v) =
        B (Submodule.Quotient.mk u) (k (Submodule.Quotient.mk v)) := by
    intro u v
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ← hB, ← hB, qRep_mk, qRep_mk, eq_comm]
  constructor
  · intro h u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact (key u v).1 (h u v)
  · intro h u v
    exact (key u v).2 (h _ _)
end GlobalTheory.HalfPairing
