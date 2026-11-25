-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:10.796817+00:00
-- url     : https://prove2.me/submissions/7021fdfe-48ae-4c57-b6dc-84e82b4a89a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_GlobalTheory_MaxLatStruct_mem_of_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution (T : Finset (Ideal R)) (hT : ∀ P, P ∈ T ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P)
    (hloc : ∀ P ∈ T, ∃ y ∈ dual h M, (∀ p ∈ P, p • y ∈ M) ∧
      ∀ z ∈ dual h M, ∃ s ∉ P, ∃ c : R, s • z - c • y ∈ M) :
    Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[R] (R ⧸ M.colon (dual h M : Set V))) := by
  choose! y hy1 hy2 hy3 using hloc
  set g := ∑ P ∈ T, y P with hg
  have hgd : g ∈ dual h M := Submodule.sum_mem _ hy1
  have hgen : ∀ z ∈ dual h M, z ∈ M ⊔ Submodule.span R {g} := by
    intro z hz
    refine mem_of_local _ _ fun Q hQ => ?_
    by_cases hQT : Q ∈ T
    · obtain ⟨s, hs1, c, hc⟩ := hy3 Q hQT z hz
      have hnle : ¬ ∏ P ∈ T.erase Q, P ≤ Q := by
        intro hle
        obtain ⟨P, hP, hPQ⟩ := (Ideal.IsPrime.prod_le hQ.isPrime).1 hle
        exact Finset.ne_of_mem_erase hP
          (((hT P).1 (Finset.mem_of_mem_erase hP)).1.eq_of_le hQ.ne_top hPQ)
      obtain ⟨t, ht1, ht2⟩ := Set.not_subset.1 hnle
      refine ⟨t * s, fun hm => (hQ.isPrime.mem_or_mem hm).elim ht2 hs1, ?_⟩
      have h1 : t • ∑ P ∈ T.erase Q, y P ∈ M := by
        rw [Finset.smul_sum]
        exact Submodule.sum_mem _ fun P hP => hy2 P (Finset.mem_of_mem_erase hP) t
          (Ideal.dvd_iff_le.1 (Finset.dvd_prod_of_mem _ hP) ht1)
      have e : (t * s) • z = (t • (s • z - c • y Q) - c • t • ∑ P ∈ T.erase Q, y P) + (c * t) • g := by
        rw [hg, ← Finset.add_sum_erase T y hQT]
        module
      rw [e]
      exact Submodule.add_mem_sup (M.sub_mem (M.smul_mem _ hc) (M.smul_mem _ h1))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
    · have hle : ¬ M.colon (dual h M : Set V) ≤ Q := fun hle => hQT ((hT Q).2 ⟨hQ, hle⟩)
      obtain ⟨s, hs1, hs2⟩ := Set.not_subset.1 hle
      exact ⟨s, hs2, Submodule.mem_sup_left (Submodule.mem_colon.1 hs1 _ hz)⟩
  let f : R →ₗ[R] (↥(dual h M) ⧸ M.comap (dual h M).subtype) :=
    LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk ⟨g, hgd⟩)
  have hf : ∀ r, f r = Submodule.Quotient.mk (r • ⟨g, hgd⟩) := fun r => rfl
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 (hgen z z.2)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    refine ⟨a, ?_⟩
    rw [hf, Submodule.Quotient.eq, Submodule.mem_comap]
    change a • g - (z : V) ∈ M
    rw [← e, sub_add_cancel_right]
    exact M.neg_mem hm
  have hker : LinearMap.ker f = M.colon (dual h M : Set V) := by
    ext r
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_colon]
    change r • g ∈ M ↔ _
    refine ⟨fun hr z hz => ?_, fun hr => hr g hgd⟩
    obtain ⟨m, hm, u, hu, rfl⟩ := Submodule.mem_sup.1 (hgen z hz)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [smul_add, smul_comm r a]
    exact M.add_mem (M.smul_mem _ hm) (M.smul_mem _ hr)
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)).symm⟩
end GlobalTheory.MaxLatStruct
