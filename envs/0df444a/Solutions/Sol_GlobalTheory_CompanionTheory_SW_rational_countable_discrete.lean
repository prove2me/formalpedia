-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.rational_countable_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:01.860811+00:00
-- url     : https://prove2.me/submissions/e0297c7a-cbe1-4161-814b-0500917a9074

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNhdsZeroPrincipalEqZero
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArithmeticUnitaryGroupDiscrete
import Theorems.Thm_GlobalTheory_AdeleDiscrete_exists_nhds_zero_principal_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  intro F E _ _ _ _ _ σ hσ M J _
  have hfr : Module.finrank F E = 2 := hσ.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  constructor
  · have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    have : Countable (Matrix (Fin M) (Fin M) E) :=
      inferInstanceAs (Countable (Fin M → Fin M → E))
    have : Countable (GL (Fin M) E) :=
      (Units.val_injective : Function.Injective
        (Units.val : GL (Fin M) E → Matrix (Fin M) (Fin M) E)).countable
    have hS : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin
      rw [Subgroup.coe_map]
      exact (Set.to_countable _).image _
    have := hS.to_subtype
    let f : HFinIn (AF F) σ J → (HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :=
      fun g => ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩
    have hf : Function.Injective f := by
      intro x y h
      have h' : (f x).1 = (f y).1 := by rw [h]
      exact Subtype.ext (Subtype.ext h')
    exact hf.countable
  · obtain ⟨W, hW, hWp⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (AF F) b
    have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
    let m : HA (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
      fun h => ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    have hm : Continuous m := Units.continuous_val.comp continuous_subtype_val
    have hm1 : m 1 = 1 := rfl
    let e : HA (AF F) σ J → Fin M → Fin M → _ → AF F := fun h i j k =>
      B.coord k (m h i j) - B.coord k ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    refine ⟨⋂ i, ⋂ j, ⋂ k, (fun h => e h i j k) ⁻¹' W,
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => Filter.iInter_mem.2 fun k => ?_, ?_⟩
    · have hce : Continuous fun h => e h i j k :=
        ((hc k).comp (hm.matrix_elem i j)).sub continuous_const
      refine hce.continuousAt.preimage_mem_nhds ?_
      have : e 1 i j k = 0 := by
        show B.coord k (m 1 i j) - _ = 0
        rw [hm1, sub_self]
      rw [this]; exact hW
    · intro h hU hh
      obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 hh
      have hent : ∀ i j, m h i j = inclR (F := F) (AF F) ((γ : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        show ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = _
        rw [← hγ]
        rfl
      have hco : ∀ (x : E) k, B.coord k (inclR (F := F) (AF F) x) =
          algebraMap F (AF F) (b.repr x k) := by
        intro x k
        show B.repr ((1 : AF F) ⊗ₜ[F] x) k = _
        rw [Algebra.TensorProduct.basis_repr_tmul]
        simp
      have hone : ∀ i j, (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j =
          inclR (F := F) (AF F) ((1 : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have hγ1 : (γ : Matrix (Fin M) (Fin M) E) = 1 := by
        ext i j
        refine b.repr.injective (Finsupp.ext fun k => ?_)
        have hk : e h i j k ∈ W := by
          have := Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hU i) j) k
          exact this
        have hk' : algebraMap F (AF F)
            (b.repr ((γ : Matrix (Fin M) (Fin M) E) i j) k -
              b.repr ((1 : Matrix (Fin M) (Fin M) E) i j) k) ∈ W := by
          rw [map_sub, ← hco, ← hco, ← hent, ← hone]
          exact hk
        exact sub_eq_zero.1 (hWp _ hk')
      have hγ2 : γ = 1 := Units.ext hγ1
      have hfin : HA.mat (AF F) σ J h = 1 := by
        rw [← hγ, hγ2, map_one]
      exact Subtype.ext hfin
end GlobalTheory.CompanionTheory.SW
