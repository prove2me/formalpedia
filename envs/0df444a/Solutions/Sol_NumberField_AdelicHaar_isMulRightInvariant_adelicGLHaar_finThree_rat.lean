-- Prove2me | solution 1 for NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar_finThree_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3f1f186c-c059-5c67-8b06-8f65ff19cca4

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat

set_option autoImplicit false

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace UnimodularAdelicGL3

section Countability

open NumberField IsDedekindDomain TopologicalSpace Topology
open scoped MatrixGroups

open LanglandsTunnell.CubicInduction

namespace AdelicCountability

private theorem countable_ideal (R : Type*) [CommRing R] [IsNoetherianRing R] [Countable R] : Countable (Ideal R) := by
  have hfg : ∀ I : Ideal R, ∃ s : Finset R, Ideal.span (s : Set R) = I := fun I => IsNoetherian.noetherian I
  choose gen hgen using hfg
  have hinj : Function.Injective gen := fun I J h => by rw [← hgen I, ← hgen J, h]
  exact hinj.countable

private scoped instance countable_ringOfIntegers_rat : Countable (𝓞 ℚ) :=
  Countable.of_module_finite ℤ (𝓞 ℚ)

private scoped instance countable_heightOneSpectrum_rat : Countable (HeightOneSpectrum (𝓞 ℚ)) := by
  haveI := countable_ideal (𝓞 ℚ)
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  exact hinj.countable

private scoped instance secondCountableTopology_finiteAdeleRing_rat : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology (X := fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (C := fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    fun v => NumberField.isOpenAdicCompletionIntegers ℚ v

private theorem isReal_of_rat' (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private scoped instance secondCountableTopology_completion_rat (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (isReal_of_rat' w)).isEmbedding.secondCountableTopology

private scoped instance secondCountableTopology_infiniteAdeleRing_rat : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))

private scoped instance secondCountableTopology_adeleRing_rat : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private theorem secondCountableTopology_matrix3 (A : Type*) [TopologicalSpace A] [SecondCountableTopology A] :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) A) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → A))

private theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

private scoped instance secondCountableTopology_adelicGL : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  haveI := secondCountableTopology_matrix3 (AdeleRing (𝓞 ℚ) ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))

private scoped instance secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  haveI := secondCountableTopology_matrix3 (InfiniteAdeleRing ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))

private scoped instance secondCountableTopology_finGL : SecondCountableTopology (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  haveI := secondCountableTopology_matrix3 (FiniteAdeleRing (𝓞 ℚ) ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))

private theorem firstCountableTopology_adelicGL : FirstCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

private theorem firstCountableTopology_archGL : FirstCountableTopology (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
    inferInstance

private theorem firstCountableTopology_finGL : FirstCountableTopology (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstance

end AdelicCountability
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end Countability
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section LevelSet

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

open LanglandsTunnell.CubicInduction

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_componentAt3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_localToAdelic3 (h : LocalGL3 v) :
    ((localToAdelic3 v h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) :=
  rfl

private theorem componentAt3_localToAdelic3_self (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw, Units.val_one]

private theorem archComponent3_localToAdelic3 (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

end Components
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section OpenMaximal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_setOf_forall_entry_mem {B : Set (v.adicCompletion ℚ)} (hB : IsOpen B) :
    IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, M i j ∈ B} := by
  simp_rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (continuous_id.matrix_elem i j).isOpen_preimage B hB

private theorem isOpen_localMaximalCompact3 :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hI : IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
      ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}} :=
    isOpen_setOf_forall_entry_mem v
      (by simpa using AdelicLevel.isOpen_setOf_valued_le v (1 : v.adicCompletion ℚ) one_ne_zero)
  have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (Units.val ⁻¹' {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
          ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) ∩
        ((fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
          {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
            ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) :=
    rfl
  rw [hset]
  exact (Units.continuous_val.isOpen_preimage _ hI).inter (Units.continuous_coe_inv.isOpen_preimage _ hI)

end OpenMaximal
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section LevelCompact

private scoped instance t2Space_matrixFin3_finiteAdeleRing : T2Space (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)))

private def finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) →* LocalGL3 p :=
  (componentAt3 (𝓞 ℚ) ℚ p).comp (finEmbedN (Fin 3) (𝓞 ℚ) ℚ)

private theorem finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    finComponent3 p k = componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) := rfl

private theorem finComponent3_localEmbedN_self (p : HeightOneSpectrum (𝓞 ℚ)) (τ : LocalGL3 p) :
    finComponent3 p (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = τ :=
  componentAt3_localToAdelic3_self p τ

private theorem finComponent3_localEmbedN_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (τ : LocalGL3 p) :
    finComponent3 q (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = 1 :=
  componentAt3_localToAdelic3_of_ne p hq τ

private theorem coe_finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (i j
    : Fin 3) :
    ((finComponent3 p k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      ((k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) p :=
  rfl

private def integralMatrices : Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  {m | ∀ i j, m i j ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem isCompact_integralMatrices : IsCompact integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => AdelicBox.isCompact_integralFiniteAdeles ℚ

private theorem isClosed_range_embedProduct_matrix :
    IsClosed (Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)))) := by
  have h : Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      {q : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) × (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ |
        q.1 * MulOpposite.unop q.2 = 1 ∧ MulOpposite.unop q.2 * q.1 = 1} := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨q.1, MulOpposite.unop q.2, h1, h2⟩, Prod.ext rfl (MulOpposite.op_unop q.2)⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

private def integralPoints : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ⁻¹' (integralMatrices ×ˢ (MulOpposite.op ''
      integralMatrices))

private theorem isCompact_integralPoints : IsCompact integralPoints :=
  (Units.isInducing_embedProduct (M := Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))).isCompact_preimage
    isClosed_range_embedProduct_matrix
    (isCompact_integralMatrices.prod (isCompact_integralMatrices.image MulOpposite.continuous_op))

private theorem mem_integralPoints_of_forall_mem_localMaximalCompact3 {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    k ∈ integralPoints := by
  show (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ integralMatrices ∧
    MulOpposite.op ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        ∈ MulOpposite.op '' integralMatrices
  refine ⟨fun i j p => ?_, Set.mem_image_of_mem _ fun i j p => ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply]
    exact (hk p).1 i j
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply, map_inv]
    exact (hk p).2 i j

open scoped Classical in

private theorem exists_isCompact_superset_of_finset (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p),
      (∀ p ∈ S, IsCompact (K' p : Set (LocalGL3 p))) → (∀ p ∉ S, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      ∃ C : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact C ∧ {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀
          p, finComponent3 p k ∈ K' p} ⊆ C := by
  refine Finset.induction_on S ?_ ?_
  · intro K' _ hmax
    refine ⟨integralPoints, isCompact_integralPoints, fun k hk => ?_⟩
    exact mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
      rw [← hmax p (by simp)]
      exact hk p
  · intro p S hpS ih K' hcpt hmax
    obtain ⟨C', hC', hsub'⟩ := ih (Function.update K' p (localMaximalCompact3 (𝓞 ℚ) ℚ p))
      (fun q hq => by
        have hqp : q ≠ p := fun h => hpS (h ▸ hq)
        rw [Function.update_of_ne hqp]
        exact hcpt q (Finset.mem_insert_of_mem hq))
      (fun q hq => by
        by_cases hqp : q = p
        · subst hqp
          exact Function.update_self ..
        · rw [Function.update_of_ne hqp]
          exact hmax q fun h => hq ((Finset.mem_insert.mp h).elim (fun h' => absurd h' hqp) id))
    have hKp : IsCompact (K' p : Set (LocalGL3 p)) := hcpt p (Finset.mem_insert_self p S)
    obtain ⟨T, hT⟩ := hKp.elim_finite_subcover
      (fun τ : LocalGL3 p => {x : LocalGL3 p | τ⁻¹ * x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p})
      (fun τ => (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_localMaximalCompact3 p))
      (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp only [Set.mem_setOf_eq, inv_mul_cancel]; exact one_mem _⟩)
    refine ⟨⋃ τ ∈ T, (fun k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) => localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ * k) '' C',
      T.finite_toSet.isCompact_biUnion fun τ _ => hC'.image (continuous_const.mul continuous_id), fun k hk => ?_⟩
    obtain ⟨τ, hτT, hτ⟩ := Set.mem_iUnion₂.mp (hT (hk p))
    refine Set.mem_biUnion hτT ⟨(localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ)⁻¹ * k, hsub' fun q => ?_, mul_inv_cancel_left _ _⟩
    rw [map_mul, map_inv]
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self, finComponent3_localEmbedN_self]
      exact hτ
    · rw [Function.update_of_ne hqp, finComponent3_localEmbedN_of_ne hqp, inv_one, one_mul]
      exact hk q

private theorem exists_isCompact_forall_componentAt3_finEmbedN_mem_subset
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ C : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact C ∧
      {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ⊆
          C := by
  have hfin := Filter.eventually_cofinite.mp hcof
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_of_finset hfin.toFinset K' (fun p _ => hcpt p)
    (fun p hp => by simpa using hp)
  exact ⟨C, hC, fun k hk => hsub fun p => hk p⟩

private theorem continuous_finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (finComponent3 p) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_val.matrix_elem i j)
  · simp only [← map_inv]
    exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_coe_inv.matrix_elem i j)

private def levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) : Subgroup (GL (Fin 3)
    (FiniteAdeleRing (𝓞 ℚ) ℚ)) where
  carrier := {k | ∀ p, finComponent3 p k ∈ K' p}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro p
    rw [map_one]
    exact one_mem _
  mul_mem' := by
    intro a b ha hb p
    rw [map_mul]
    exact mul_mem (ha p) (hb p)
  inv_mem' := by
    intro a ha p
    rw [map_inv]
    exact inv_mem (ha p)

private theorem mem_levelSubgroup_iff (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) (k : (GL (Fin 3)
    (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    k ∈ levelSubgroup K' ↔ ∀ p, finComponent3 p k ∈ K' p := Iff.rfl

private theorem coe_levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    (levelSubgroup K' : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p}
          := rfl

private theorem isOpen_integralMatrices : IsOpen integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => AdelicBox.isOpen_integralFiniteAdeles ℚ

private theorem isOpen_integralPoints : IsOpen integralPoints :=
  Units.continuous_embedProduct.isOpen_preimage _
    (isOpen_integralMatrices.prod (MulOpposite.opHomeomorph.isOpenMap _ isOpen_integralMatrices))

private theorem finComponent3_mem_localMaximalCompact3_of_mem_integralPoints {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ)
    ℚ))} (hk : k ∈ integralPoints)
    (p : HeightOneSpectrum (𝓞 ℚ)) : finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨m, hm, hmk⟩ := h2
  have hmk' : MulOpposite.op m = MulOpposite.op ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin
      3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hmk
  have hm' : m = ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
      MulOpposite.op_injective hmk'
  subst hm'
  change _ ∧ _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1 i j p
  · rw [← map_inv, coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hm i j p

private theorem one_mem_integralPoints : (1 : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈ integralPoints :=
  mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
    rw [map_one]
    exact one_mem _

open scoped Classical in

private theorem isOpen_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K'
        p} := by
  rw [← coe_levelSubgroup]
  refine Subgroup.isOpen_of_mem_nhds (levelSubgroup K') (g := 1) ?_
  have hfin := Filter.eventually_cofinite.mp hcof
  have hW : IsOpen (integralPoints ∩ ⋂ p ∈ hfin.toFinset, finComponent3 p ⁻¹' (K' p : Set (LocalGL3 p))) :=
    isOpen_integralPoints.inter
      (isOpen_biInter_finset fun p _ => (continuous_finComponent3 p).isOpen_preimage _ (hopen p))
  refine Filter.mem_of_superset (hW.mem_nhds ⟨one_mem_integralPoints, ?_⟩) ?_
  · exact Set.mem_iInter₂.mpr fun p _ => by
      show finComponent3 p 1 ∈ K' p
      rw [map_one]
      exact one_mem _
  · intro k hk
    obtain ⟨hint, hS⟩ := hk
    rw [SetLike.mem_coe, mem_levelSubgroup_iff]
    intro p
    by_cases hp : p ∈ hfin.toFinset
    · exact Set.mem_iInter₂.mp hS p hp
    · have hmax : K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by simpa using hp
      rw [hmax]
      exact finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hint p

private theorem isCompact_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsCompact {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈
        K' p} := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_forall_componentAt3_finEmbedN_mem_subset K' hcpt hcof
  have hclosed : IsClosed {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3)
      (𝓞 ℚ) ℚ k) ∈ K' p} := by
    rw [← coe_levelSubgroup]
    exact Subgroup.isClosed_of_isOpen _ (isOpen_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcof)
  exact hC.of_isClosed_subset hclosed hsub

end LevelCompact
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end LevelSet
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section ArchimedeanEmbedding

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

noncomputable section

open LanglandsTunnell.CubicInduction

section ArchEmbedding

private def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j =>
    ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

private theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

private theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

private def archToAdelic3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

private theorem coe_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ((archToAdelic3 g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

private theorem archComponent3_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archToAdelic3 g) = g := by
  apply Units.ext
  rw [coe_archComponent3, coe_archToAdelic3, mapMatrix_arch_archMat3]

private theorem componentAt3_archToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archToAdelic3 g) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_archToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_archMat3, map_one, Units.val_one]

end ArchEmbedding
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end ArchimedeanEmbedding
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section ComponentCalculus

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped MatrixGroups

open LanglandsTunnell.CubicInduction

private theorem adelicGL3_ext {g g' : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hfin : ∀ u : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ u g = componentAt3 (𝓞 ℚ) ℚ u g')
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ g') : g = g' := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · exact congrArg Units.val harch
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun u => ?_
    exact congrArg Units.val (hfin u)

private theorem continuous_finEmbedN3 : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        ((k⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
        AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

private theorem continuous_archToAdelic3 : Continuous archToAdelic3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

end ComponentCalculus
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section ArchimedeanFiniteSplitting

open Matrix IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

open scoped NNReal ENNReal

noncomputable section

open LanglandsTunnell.CubicInduction

private theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f))

private def finPart3 : AdelicGL 3 (𝓞 ℚ) ℚ →* (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((finPart3 g : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem continuous_finPart3 : Continuous finPart3 :=
  continuous_generalLinearGroup_map _ (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)

private theorem continuous_archComponent3 : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
  continuous_generalLinearGroup_map _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem coe_finEmbedN3 (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem archComponent3_finEmbedN (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : archComponent3 (𝓞 ℚ) ℚ
    (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_finEmbedN3, mapMatrix_arch_finMatN, Units.val_one]

private theorem finPart3_finEmbedN (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : finPart3 (finEmbedN (Fin 3) (𝓞 ℚ) ℚ
    k) = k := by
  apply Units.ext
  rw [coe_finPart3, coe_finEmbedN3, mapMatrix_fin_finMatN]

private theorem finPart3_archToAdelic3 (a : (GL (Fin 3) (InfiniteAdeleRing ℚ))) : finPart3 (archToAdelic3 a) = 1 := by
  apply Units.ext
  rw [coe_finPart3, coe_archToAdelic3, mapMatrix_fin_archMat3, Units.val_one]

private theorem componentAt3_finEmbedN_finPart3 (u : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ u (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g)) = componentAt3 (𝓞 ℚ) ℚ u g := by
  apply Units.ext
  rw [coe_componentAt3, coe_componentAt3, coe_finEmbedN3, coe_finPart3, ← RingHom.mapMatrix_comp,
    RingHom.comp_apply, RingHom.comp_apply, mapMatrix_fin_finMatN]

private def archFinMul (p : (GL (Fin 3) (InfiniteAdeleRing ℚ)) × (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : AdelicGL 3
    (𝓞 ℚ) ℚ :=
  archToAdelic3 p.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ p.2

private theorem continuous_archFinMul : Continuous archFinMul :=
  (continuous_archToAdelic3.comp continuous_fst).mul (continuous_finEmbedN3.comp continuous_snd)

private theorem archComponent3_archFinMul (p : (GL (Fin 3) (InfiniteAdeleRing ℚ)) × (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ)
    ℚ))) : archComponent3 (𝓞 ℚ) ℚ (archFinMul p) = p.1 := by
  rw [archFinMul, map_mul, archComponent3_archToAdelic3, archComponent3_finEmbedN, mul_one]

private theorem finPart3_archFinMul (p : (GL (Fin 3) (InfiniteAdeleRing ℚ)) × (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    finPart3 (archFinMul p) = p.2 := by
  rw [archFinMul, map_mul, finPart3_archToAdelic3, finPart3_finEmbedN, one_mul]

private theorem archFinMul_archComponent3_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archFinMul (archComponent3 (𝓞 ℚ) ℚ g, finPart3 g) = g := by
  refine adelicGL3_ext (fun u => ?_) ?_
  · simp only [archFinMul, map_mul, componentAt3_archToAdelic3, one_mul, componentAt3_finEmbedN_finPart3]
  · rw [archComponent3_archFinMul]

private def archFinHomeomorph : (GL (Fin 3) (InfiniteAdeleRing ℚ)) × (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ≃ₜ AdelicGL
    3 (𝓞 ℚ) ℚ where
  toFun := archFinMul
  invFun g := (archComponent3 (𝓞 ℚ) ℚ g, finPart3 g)
  left_inv p := by simp only [archComponent3_archFinMul, finPart3_archFinMul]
  right_inv g := archFinMul_archComponent3_finPart3 g
  continuous_toFun := continuous_archFinMul
  continuous_invFun := continuous_archComponent3.prodMk continuous_finPart3

private theorem archFinHomeomorph_apply (p : (GL (Fin 3) (InfiniteAdeleRing ℚ)) × (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ)
    ℚ))) : archFinHomeomorph p = archFinMul p := rfl

private theorem regular_adelicGLHaar : (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).Regular := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  show (Measure.haar : Measure (AdelicGL 3 (𝓞 ℚ) ℚ)).Regular
  infer_instance

private scoped instance sigmaCompactSpace_adelicGL : SigmaCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

private theorem innerRegular_adelicGLHaar : (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).InnerRegular := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := regular_adelicGLHaar
  infer_instance

private theorem mul_mem_integralPoints {k k' : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))} (hk : k ∈ integralPoints) (hk' :
    k' ∈ integralPoints) :
    k * k' ∈ integralPoints :=
  mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
    rw [map_mul]
    exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).mul_mem (finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hk p)
      (finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hk' p)

private theorem inv_mem_integralPoints {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))} (hk : k ∈ integralPoints) : k⁻¹ ∈
    integralPoints :=
  mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
    rw [map_inv]
    exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).inv_mem (finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hk p)

private theorem preimage_mul_finEmbedN_image_archFinMul_prod_integralPoints (C : Set (GL (Fin 3) (InfiniteAdeleRing
    ℚ))) {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (hk : k ∈ integralPoints) :
    (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => x * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ⁻¹' (archFinMul '' (C ×ˢ integralPoints)) =
      archFinMul '' (C ×ˢ integralPoints) := by
  ext x
  constructor
  · rintro ⟨⟨a, k'⟩, ⟨ha, hk'⟩, hx⟩
    refine ⟨(a, k' * k⁻¹), ⟨ha, mul_mem_integralPoints hk' (inv_mem_integralPoints hk)⟩, ?_⟩
    have hx' : archToAdelic3 a * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k' = x * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k := hx
    show archToAdelic3 a * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (k' * k⁻¹) = x
    rw [map_mul, map_inv, ← mul_assoc, hx', mul_inv_cancel_right]
  · rintro ⟨⟨a, k'⟩, ⟨ha, hk'⟩, rfl⟩
    refine ⟨(a, k' * k), ⟨ha, mul_mem_integralPoints hk' hk⟩, ?_⟩
    show archToAdelic3 a * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (k' * k) =
      archToAdelic3 a * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k' * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k
    rw [map_mul, mul_assoc]

private theorem modularCharacterFun_finEmbedN_eq_one_of_mem_integralPoints {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (hk : k ∈ integralPoints) :
    modularCharacterFun (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := innerRegular_adelicGLHaar
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → InfiniteAdeleRing ℚ))
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : (GL (Fin 3) (InfiniteAdeleRing ℚ)))
  set S : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := archFinMul '' (C ×ˢ integralPoints) with hS
  have hScpt : IsCompact S := (hC.prod isCompact_integralPoints).image continuous_archFinMul
  have hSmeas : MeasurableSet S := hScpt.isClosed.measurableSet
  have hSfin : adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ S ≠ ⊤ := hScpt.measure_lt_top.ne
  have hSpos : adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ S ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (measure_mono (Set.image_mono (Set.prod_mono interior_subset le_rfl)))).ne'
    have hopen : IsOpen (archFinMul '' (interior C ×ˢ integralPoints)) :=
      archFinHomeomorph.isOpenMap _ (isOpen_interior.prod isOpen_integralPoints)
    exact hopen.measure_pos _
      ⟨archFinMul (1, 1), (1, 1), ⟨mem_interior_iff_mem_nhds.mpr hC1, one_mem_integralPoints⟩, rfl⟩
  have h : Measure.map (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => x * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k)
      (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) S =
        (modularCharacterFun (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) • adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) S := by
    rw [map_right_mul_eq_modularCharacterFun_smul]
  rw [Measure.map_apply (measurable_mul_const _) hSmeas, hS,
    preimage_mul_finEmbedN_image_archFinMul_prod_integralPoints C hk, ← hS, Measure.smul_apply, ENNReal.smul_def] at h
  have h2 : ((modularCharacterFun (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) : ℝ≥0) : ℝ≥0∞) *
      adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ S = (1 : ℝ≥0∞) * adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ S := by
    rw [one_mul]
    exact h.symm
  exact_mod_cast (ENNReal.mul_left_inj hSpos hSfin).mp h2

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end ArchimedeanFiniteSplitting
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section HomomorphismsOfGL3

open Matrix

namespace GL3Hom

section Generic

variable {G : Type*} [Group G] {M : Type*} [CommMonoid M] (Δ : G →* M)

private theorem map_mul_map_inv (a : G) : Δ a * Δ a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem map_conj_eq (a b : G) : Δ (a * b * a⁻¹) = Δ b := by
  rw [map_mul, map_mul, mul_right_comm, map_mul_map_inv, one_mul]

private theorem map_commutator_eq_one (a b : G) : Δ (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [map_mul, map_conj_eq, map_mul_map_inv]

end Generic
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

private theorem eq_one_of_pow_three_eq_one {x : NNReal} (h : x ^ 3 = 1) : x = 1 :=
  (pow_eq_one_iff_of_nonneg (zero_le : (0 : NNReal) ≤ x) (by norm_num)).1 h

section GL3

variable {F : Type*} [Field F]

private def diagonalUnit (d : Fin 3 → Fˣ) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun k => (d k : F)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun k _ => (d k).ne_zero)

private theorem diagonalUnit_val (d : Fin 3 → Fˣ) :
    (diagonalUnit d : Matrix (Fin 3) (Fin 3) F) = diagonal fun k => (d k : F) :=
  rfl

private theorem diagonalUnit_inv (d : Fin 3 → Fˣ) : (diagonalUnit d)⁻¹ = diagonalUnit fun k => (d k)⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, diagonalUnit_val, diagonalUnit_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  funext k
  exact Units.mul_inv (d k)

private theorem diagonalUnit_const_mul_comm (c : Fˣ) (x : GL (Fin 3) F) :
    diagonalUnit (fun _ => c) * x = x * diagonalUnit fun _ => c := by
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, diagonalUnit_val, diagonal_mul, mul_diagonal, mul_comm]

private def coordinateUnit (k : Fin 3) (x : Fˣ) : GL (Fin 3) F :=
  diagonalUnit (Function.update (fun _ => (1 : Fˣ)) k x)

private theorem diagonalUnit_eq_prod (d : Fin 3 → Fˣ) :
    diagonalUnit d = coordinateUnit 0 (d 0) * coordinateUnit 1 (d 1) * coordinateUnit 2 (d 2) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [coordinateUnit, Units.val_mul, diagonalUnit_val, diagonal_mul_diagonal, diagonal_apply]
  split_ifs with hij
  · fin_cases i <;> simp
  · rfl

private def swapMatrix₀₁ : Matrix (Fin 3) (Fin 3) F :=
  of ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]

private def swapMatrix₀₂ : Matrix (Fin 3) (Fin 3) F :=
  of ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

private theorem det_swapMatrix₀₁_ne_zero : (swapMatrix₀₁ : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  rw [det_fin_three]
  simp [swapMatrix₀₁]

private theorem det_swapMatrix₀₂_ne_zero : (swapMatrix₀₂ : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  rw [det_fin_three]
  simp [swapMatrix₀₂]

private def swapUnit₀₁ : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero swapMatrix₀₁ det_swapMatrix₀₁_ne_zero

private def swapUnit₀₂ : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero swapMatrix₀₂ det_swapMatrix₀₂_ne_zero

private theorem swapUnit₀₁_val : ((swapUnit₀₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMatrix₀₁ := rfl

private theorem swapUnit₀₂_val : ((swapUnit₀₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMatrix₀₂ := rfl

private theorem swapUnit₀₁_inv : (swapUnit₀₁ : GL (Fin 3) F)⁻¹ = swapUnit₀₁ := by
  apply inv_eq_of_mul_eq_one_right
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, swapUnit₀₁_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [swapMatrix₀₁, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swapUnit₀₂_inv : (swapUnit₀₂ : GL (Fin 3) F)⁻¹ = swapUnit₀₂ := by
  apply inv_eq_of_mul_eq_one_right
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, swapUnit₀₂_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [swapMatrix₀₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swapUnit₀₁_mul_coordinateUnit_mul_inv (x : Fˣ) :
    swapUnit₀₁ * coordinateUnit 0 x * swapUnit₀₁⁻¹ = coordinateUnit 1 x := by
  rw [swapUnit₀₁_inv]
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, swapUnit₀₁_val, coordinateUnit, coordinateUnit, diagonalUnit_val,
    diagonalUnit_val]
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix₀₁, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal, Function.update_apply]

private theorem swapUnit₀₂_mul_coordinateUnit_mul_inv (x : Fˣ) :
    swapUnit₀₂ * coordinateUnit 0 x * swapUnit₀₂⁻¹ = coordinateUnit 2 x := by
  rw [swapUnit₀₂_inv]
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, swapUnit₀₂_val, coordinateUnit, coordinateUnit, diagonalUnit_val,
    diagonalUnit_val]
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix₀₂, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal, Function.update_apply]

variable {N : Type*} [CommMonoid N]

private theorem map_coordinateUnit_eq (Δ : GL (Fin 3) F →* N) (k : Fin 3) (x : Fˣ) :
    Δ (coordinateUnit k x) = Δ (coordinateUnit 0 x) := by
  fin_cases k
  · rfl
  · show Δ (coordinateUnit 1 x) = Δ (coordinateUnit 0 x)
    rw [← swapUnit₀₁_mul_coordinateUnit_mul_inv x, map_conj_eq]
  · show Δ (coordinateUnit 2 x) = Δ (coordinateUnit 0 x)
    rw [← swapUnit₀₂_mul_coordinateUnit_mul_inv x, map_conj_eq]

private theorem map_coordinateUnit_eq_one (Δ : GL (Fin 3) F →* NNReal)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (x : Fˣ) :
    Δ (coordinateUnit 0 x) = 1 := by
  apply eq_one_of_pow_three_eq_one
  have h := hcentral (diagonalUnit fun _ => x) (diagonalUnit_const_mul_comm x)
  rw [diagonalUnit_eq_prod, map_mul, map_mul, map_coordinateUnit_eq Δ 1, map_coordinateUnit_eq Δ 2] at h
  rw [pow_succ, pow_two]
  exact h

private theorem map_diagonalUnit_eq_one (Δ : GL (Fin 3) F →* NNReal)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (d : Fin 3 → Fˣ) :
    Δ (diagonalUnit d) = 1 := by
  rw [diagonalUnit_eq_prod, map_mul, map_mul, map_coordinateUnit_eq Δ 1, map_coordinateUnit_eq Δ 2,
    map_coordinateUnit_eq_one Δ hcentral, map_coordinateUnit_eq_one Δ hcentral,
    map_coordinateUnit_eq_one Δ hcentral, mul_one, mul_one]

private def transvectionUnit (i j : Fin 3) (hij : i ≠ j) (c : F) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (transvection i j c) (by
    rw [det_transvection_of_ne i j hij]
    exact one_ne_zero)

private theorem transvectionUnit_val (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (transvectionUnit i j hij c : Matrix (Fin 3) (Fin 3) F) = transvection i j c :=
  rfl

private theorem transvectionUnit_mul (i j : Fin 3) (hij : i ≠ j) (c c' : F) :
    transvectionUnit i j hij c * transvectionUnit i j hij c' = transvectionUnit i j hij (c + c') := by
  apply Units.ext
  rw [Units.val_mul, transvectionUnit_val, transvectionUnit_val, transvectionUnit_val,
    transvection_mul_transvection_same i j hij]

private theorem transvectionUnit_zero (i j : Fin 3) (hij : i ≠ j) : transvectionUnit i j hij (0 : F) = 1 := by
  apply Units.ext
  rw [transvectionUnit_val, transvection_zero, Units.val_one]

private theorem transvectionUnit_inv (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (transvectionUnit i j hij c)⁻¹ = transvectionUnit i j hij (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [transvectionUnit_mul, add_neg_cancel, transvectionUnit_zero]

private theorem coordinateUnit_mul_transvectionUnit_mul_inv (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) (b : F) :
    coordinateUnit i t * transvectionUnit i j hij b * (coordinateUnit i t)⁻¹ =
      transvectionUnit i j hij ((t : F) * b) := by
  rw [coordinateUnit, diagonalUnit_inv]
  apply GeneralLinearGroup.ext
  intro a a'
  rw [Units.val_mul, Units.val_mul, diagonalUnit_val, diagonalUnit_val, transvectionUnit_val,
    transvectionUnit_val, mul_diagonal, diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply, Function.update_apply]
  by_cases ha : a = i
  · subst ha
    by_cases ha' : a' = a
    · subst ha'
      simp [hij.symm]
    · by_cases hj : a' = j
      · subst hj
        simp [ha', Ne.symm ha']
      · simp [ha', Ne.symm ha', Ne.symm hj]
  · by_cases ha' : a' = i
    · subst ha'
      simp [ha, Ne.symm ha]
    · simp [ha, Ne.symm ha, ha']

private theorem transvectionUnit_eq_commutator (i j : Fin 3) (hij : i ≠ j) (c : F) (t : Fˣ) (ht : (t : F) ≠ 1) :
    transvectionUnit i j hij c =
      coordinateUnit i t * transvectionUnit i j hij (c / ((t : F) - 1)) * (coordinateUnit i t)⁻¹ *
        (transvectionUnit i j hij (c / ((t : F) - 1)))⁻¹ := by
  rw [coordinateUnit_mul_transvectionUnit_mul_inv, transvectionUnit_inv, transvectionUnit_mul]
  have h1 : (t : F) - 1 ≠ 0 := sub_ne_zero.2 ht
  have h2 : (t : F) * (c / ((t : F) - 1)) + -(c / ((t : F) - 1)) = c := by
    rw [← sub_eq_add_neg, ← sub_one_mul]
    field_simp
  exact congrArg (transvectionUnit i j hij) h2.symm

private theorem map_transvectionUnit_eq_one (Δ : GL (Fin 3) F →* N) (ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1) (i j : Fin 3)
    (hij : i ≠ j) (c : F) : Δ (transvectionUnit i j hij c) = 1 := by
  obtain ⟨t, ht0, ht1⟩ := ht
  have ht1' : ((Units.mk0 t ht0 : Fˣ) : F) ≠ 1 := by
    rw [Units.val_mk0]
    exact ht1
  rw [transvectionUnit_eq_commutator i j hij c (Units.mk0 t ht0) ht1', map_mul, map_conj_eq, map_mul_map_inv]

private theorem map_eq_one (Δ : GL (Fin 3) F →* NNReal) (ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (g : GL (Fin 3) F) : Δ g = 1 := by
  have key : ∀ A : Matrix (Fin 3) (Fin 3) F, A.det ≠ 0 →
      ∀ g' : GL (Fin 3) F, (g' : Matrix (Fin 3) (Fin 3) F) = A → Δ g' = 1 := by
    intro A hA
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun B => ∀ g' : GL (Fin 3) F, (g' : Matrix (Fin 3) (Fin 3) F) = B → Δ g' = 1) A hA ?_ ?_ ?_
    · intro D hD g' hg'
      rw [det_diagonal] at hD
      have hD' : ∀ k, D k ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hD k (Finset.mem_univ k)
      have hg'' : g' = diagonalUnit fun k => Units.mk0 (D k) (hD' k) := by
        apply Units.ext
        rw [hg', diagonalUnit_val]
        simp only [Units.val_mk0]
      rw [hg'']
      exact map_diagonalUnit_eq_one Δ hcentral _
    · intro s g' hg'
      have hg'' : g' = transvectionUnit s.i s.j s.hij s.c := by
        apply Units.ext
        rw [hg', transvectionUnit_val]
        rfl
      rw [hg'']
      exact map_transvectionUnit_eq_one Δ ht _ _ _ _
    · intro B C hB hC hPB hPC g' hg'
      have hg'' : g' = GeneralLinearGroup.mkOfDetNeZero B hB * GeneralLinearGroup.mkOfDetNeZero C hC := by
        apply Units.ext
        rw [hg', Units.val_mul]
        rfl
      rw [hg'', map_mul, hPB _ rfl, hPC _ rfl, mul_one]
  exact key _ (GeneralLinearGroup.det_ne_zero g) g rfl

end GL3
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end GL3Hom
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end HomomorphismsOfGL3
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section ModularCharacter

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Unimodular

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

private theorem modularCharacter_apply (g : G) : modularCharacter g = modularCharacterFun g :=
  rfl

section Measure

variable [MeasurableSpace G] [BorelSpace G]

private theorem modularCharacterFun_eq_one_of_central (μ : Measure G) [IsHaarMeasure μ] {z : G}
    (hz : ∀ x, z * x = x * z) : modularCharacterFun z = 1 := by
  rw [modularCharacterFun_eq_haarScalarFactor μ z]
  have h : (fun x : G => x * z) = fun x : G => z * x := funext fun x => (hz x).symm
  have hm : Measure.map (fun x : G => x * z) μ = μ := by
    rw [h]
    exact map_mul_left_eq_self μ z
  have key : ∀ (ν : Measure G) [IsHaarMeasure ν], ν = μ → haarScalarFactor ν μ = 1 := by
    rintro ν _ rfl
    exact haarScalarFactor_self ν
  exact key _ hm

private theorem isMulRightInvariant_of_forall_modularCharacterFun_eq_one (μ : Measure G) [IsHaarMeasure μ]
    [μ.InnerRegular] (h : ∀ g : G, modularCharacterFun g = 1) : IsMulRightInvariant μ :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

private theorem isMulRightInvariant_of_forall_hom_eq_one (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegular]
    (halg : ∀ Δ : G →* ℝ≥0, (∀ z : G, (∀ x, z * x = x * z) → Δ z = 1) → ∀ g, Δ g = 1) :
    IsMulRightInvariant μ :=
  isMulRightInvariant_of_forall_modularCharacterFun_eq_one μ fun g =>
    (modularCharacter_apply g).symm.trans
      (halg modularCharacter
        (fun z hz => (modularCharacter_apply z).trans (modularCharacterFun_eq_one_of_central μ hz)) g)

end Measure
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end Unimodular
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end ModularCharacter
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section LocalAndArchimedeanFactors

open Matrix IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups NNReal

noncomputable section

open LanglandsTunnell.CubicInduction

private theorem localToAdelic3_mul_comm_of_forall_mul_comm (v : HeightOneSpectrum (𝓞 ℚ)) {z : LocalGL3 v}
    (hz : ∀ x : LocalGL3 v, z * x = x * z) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    localToAdelic3 v z * y = y * localToAdelic3 v z := by
  refine adelicGL3_ext (fun u => ?_) ?_
  · rw [map_mul, map_mul]
    rcases eq_or_ne u v with rfl | huv
    · rw [componentAt3_localToAdelic3_self]
      exact hz _
    · rw [componentAt3_localToAdelic3_of_ne v huv, one_mul, mul_one]
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, one_mul, mul_one]

private theorem modularCharacterFun_localToAdelic3_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    modularCharacterFun (localToAdelic3 v h) = 1 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have key := GL3Hom.map_eq_one ((modularCharacter (G := AdelicGL 3 (𝓞 ℚ) ℚ)).comp (localToAdelic3 v))
    ⟨2, two_ne_zero, by norm_num⟩
    (fun z hz => by
      rw [MonoidHom.comp_apply, Unimodular.modularCharacter_apply]
      exact Unimodular.modularCharacterFun_eq_one_of_central (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
        (localToAdelic3_mul_comm_of_forall_mul_comm v hz))
    h
  rwa [MonoidHom.comp_apply, Unimodular.modularCharacter_apply] at key

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private def realCoord : InfiniteAdeleRing ℚ →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace)

private def ofReal (r : ℝ) : InfiniteAdeleRing ℚ :=
  show (v : InfinitePlace ℚ) → v.Completion from
    fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_of_rat v)).symm r

private theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem ofReal_realCoord (x : InfiniteAdeleRing ℚ) : ofReal (realCoord x) = x := by
  funext v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply
    (x Rat.infinitePlace)

private def realCoordEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  RingEquiv.ofBijective realCoord
    ⟨Function.LeftInverse.injective ofReal_realCoord, Function.RightInverse.surjective realCoord_ofReal⟩

private def realGL : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map (realCoordEquiv.symm : ℝ →+* InfiniteAdeleRing ℚ)

private theorem realGL_surjective : Function.Surjective realGL := fun a =>
  ⟨Matrix.GeneralLinearGroup.map (realCoordEquiv : InfiniteAdeleRing ℚ →+* ℝ) a,
    Units.ext (Matrix.ext fun i j => by simp [realGL])⟩

private theorem archToAdelic3_realGL_mul_comm_of_forall_mul_comm {z : GL (Fin 3) ℝ} (hz : ∀ x, z * x = x * z)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) : archToAdelic3 (realGL z) * y = y * archToAdelic3 (realGL z) := by
  refine adelicGL3_ext (fun u => ?_) ?_
  · rw [map_mul, map_mul, componentAt3_archToAdelic3, one_mul, mul_one]
  · rw [map_mul, map_mul, archComponent3_archToAdelic3]
    obtain ⟨x, hx⟩ := realGL_surjective (archComponent3 (𝓞 ℚ) ℚ y)
    rw [← hx, ← map_mul, ← map_mul, hz]

private theorem modularCharacterFun_archToAdelic3_eq_one (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    modularCharacterFun (archToAdelic3 a) = 1 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨a', rfl⟩ := realGL_surjective a
  have key := GL3Hom.map_eq_one
    ((modularCharacter (G := AdelicGL 3 (𝓞 ℚ) ℚ)).comp (archToAdelic3.comp realGL)) ⟨2, two_ne_zero, by norm_num⟩
    (fun z hz => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Unimodular.modularCharacter_apply]
      exact Unimodular.modularCharacterFun_eq_one_of_central (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
        (archToAdelic3_realGL_mul_comm_of_forall_mul_comm hz))
    a'
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, Unimodular.modularCharacter_apply] at key

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end LocalAndArchimedeanFactors
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section NonIntegralPlaces

open Matrix IsDedekindDomain NumberField AutomorphicForm
open scoped MatrixGroups

noncomputable section

open LanglandsTunnell.CubicInduction

private theorem eventually_finComponent3_mem_localMaximalCompact3 (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    ∀ᶠ p in Filter.cofinite, finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have h1 : ∀ᶠ p in Filter.cofinite, ∀ i j : Fin 3,
      ((k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) p ∈ p.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      RestrictedProduct.eventually _ _ ((k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
  have h2 : ∀ᶠ p in Filter.cofinite, ∀ i j : Fin 3,
      (((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) p ∈
          p.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      RestrictedProduct.eventually _ _ (((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3)
          (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
  filter_upwards [h1, h2] with p hp1 hp2
  change _ ∧ _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hp1 i j
  · rw [← map_inv, coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hp2 i j

private theorem exists_finset_forall_finComponent3_mem_localMaximalCompact3 (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ)
    ℚ))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p ∉ S, finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have h := Filter.eventually_cofinite.mp (eventually_finComponent3_mem_localMaximalCompact3 k)
  refine ⟨h.toFinset, fun p hp => ?_⟩
  by_contra hk
  exact hp (h.mem_toFinset.mpr hk)

private theorem map_eq_one_of_forall_not_mem_finset {M : Type*} [Monoid M] (Δ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    →* M)
    (hloc : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 p), Δ (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p h) = 1)
    (hint : ∀ k ∈ integralPoints, Δ k = 1) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)), (∀ p ∉ S, finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) → Δ k =
        1 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro k hk
    exact hint k (mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => hk p (Finset.notMem_empty p))
  · intro p S _ ih k hk
    have hk' : ∀ q ∉ S, finComponent3 q (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p (finComponent3 p k)⁻¹ * k) ∈
        localMaximalCompact3 (𝓞 ℚ) ℚ q := by
      intro q hq
      rw [map_mul]
      rcases eq_or_ne q p with rfl | hqp
      · rw [finComponent3_localEmbedN_self, inv_mul_cancel]
        exact one_mem _
      · rw [finComponent3_localEmbedN_of_ne hqp, one_mul]
        exact hk q fun hmem => (Finset.mem_insert.mp hmem).elim hqp hq
    have hdecomp : localEmbedN (Fin 3) (𝓞 ℚ) ℚ p (finComponent3 p k) *
        (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p (finComponent3 p k)⁻¹ * k) = k := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [← hdecomp, map_mul, hloc, ih _ hk', one_mul]

private theorem map_eq_one_of_local_of_integral {M : Type*} [Monoid M] (Δ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) →*
    M)
    (hloc : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 p), Δ (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p h) = 1)
    (hint : ∀ k ∈ integralPoints, Δ k = 1) (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Δ k = 1 := by
  obtain ⟨S, hS⟩ := exists_finset_forall_finComponent3_mem_localMaximalCompact3 k
  exact map_eq_one_of_forall_not_mem_finset Δ hloc hint S k hS

private theorem finEmbedN_localEmbedN (p : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 p) :
    finEmbedN (Fin 3) (𝓞 ℚ) ℚ (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p h) = localToAdelic3 p h :=
  rfl

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end NonIntegralPlaces
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

section TrivialModularCharacter

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField NumberField.AdelicHaar MeasureTheory MeasureTheory.Measure IsDedekindDomain
open scoped MatrixGroups

open LanglandsTunnell.CubicInduction

private theorem modularCharacterFun_finEmbedN_eq_one (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    modularCharacterFun (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  have key := map_eq_one_of_local_of_integral
    ((modularCharacter (G := AdelicGL 3 (𝓞 ℚ) ℚ)).comp (finEmbedN (Fin 3) (𝓞 ℚ) ℚ))
    (fun p h => by
      rw [MonoidHom.comp_apply, finEmbedN_localEmbedN, Unimodular.modularCharacter_apply]
      exact modularCharacterFun_localToAdelic3_eq_one p h)
    (fun k hk => by
      rw [MonoidHom.comp_apply, Unimodular.modularCharacter_apply]
      exact modularCharacterFun_finEmbedN_eq_one_of_mem_integralPoints hk)
    k
  rwa [MonoidHom.comp_apply, Unimodular.modularCharacter_apply] at key

private theorem modularCharacterFun_adelicGL_eq_one (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modularCharacterFun g = 1 := by
  obtain ⟨p, rfl⟩ := archFinHomeomorph.surjective g
  rw [archFinHomeomorph_apply, archFinMul, ← Unimodular.modularCharacter_apply, map_mul,
    Unimodular.modularCharacter_apply, Unimodular.modularCharacter_apply, modularCharacterFun_archToAdelic3_eq_one,
    modularCharacterFun_finEmbedN_eq_one, mul_one]

end TrivialModularCharacter
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability"

end UnimodularAdelicGL3
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3.AdelicCountability P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat.UnimodularAdelicGL3"

open NumberField NumberField.AdelicHaar

theorem solution :
    (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsMulRightInvariant := by
  haveI : BorelSpace (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := UnimodularAdelicGL3.innerRegular_adelicGLHaar
  exact UnimodularAdelicGL3.Unimodular.isMulRightInvariant_of_forall_modularCharacterFun_eq_one _
    UnimodularAdelicGL3.modularCharacterFun_adelicGL_eq_one

end S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat
end P2MW
export P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat (solution)
