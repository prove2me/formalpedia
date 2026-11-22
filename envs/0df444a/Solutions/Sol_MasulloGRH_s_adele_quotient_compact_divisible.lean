-- Prove2me | solution 1 for MasulloGRH.s_adele_quotient_compact_divisible
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-21T12:41:10.303176+00:00
-- url     : https://prove2.me/submissions/ad7dd38b-5ed6-46b5-89ef-8f90361023f9

import Definitions.Def_MasulloGRH_SAdeles
import Definitions.Def_NumberField_AdelicBox

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain MasulloGRH

noncomputable section

namespace SAdeleQuotientProof

variable {F : Type*} [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma mem_SIntegers {ξ : F} :
    ξ ∈ SIntegers Sf ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → v.valuation F ξ ≤ 1 :=
  Iff.rfl

lemma mem_lattice {x : SAdeleRing F Sf} :
    x ∈ sIntegerLattice Sf ↔ ∃ ξ : F, ξ ∈ SIntegers Sf ∧ sDiagonal Sf ξ = x :=
  Iff.rfl

lemma algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (ξ : F) :
    algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F ↔
      v.valuation F ξ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap F (v.adicCompletion F) ξ = (ξ : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

open scoped Classical in
lemma exists_isOpen_subset_infiniteBox :
    ∃ U : Set (InfiniteAdeleRing F), IsOpen U ∧ U.Nonempty ∧ U ⊆ AdelicBox.infiniteBox F := by
  set b := mixedEmbedding.latticeBasis F with hb
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
  let V : Set (mixedEmbedding.mixedSpace F) := {m | ∀ i, b.repr m i ∈ Set.Ioo (0 : ℝ) 1}
  have hVopen : IsOpen V := by
    have : V = ⋂ i, (fun m => b.repr m i) ⁻¹' Set.Ioo (0 : ℝ) 1 := by ext m; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => IsOpen.preimage ?_ isOpen_Ioo
    exact (b.coord i).continuous_of_finiteDimensional
  have hVsub : V ⊆ ZSpan.fundamentalDomain b := fun m hm i => Set.Ioo_subset_Ico_self (hm i)
  refine ⟨e ⁻¹' V, hVopen.preimage (AdelicBox.continuous_ringEquiv_mixedSpace F),
    ⟨e.symm (b.equivFun.symm fun _ => 1 / 2), ?_⟩, fun x hx => hVsub hx⟩
  show e (e.symm _) ∈ V
  rw [RingEquiv.apply_symm_apply]
  intro i
  rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  norm_num

/-- Every `S`-adele can be translated by an `S`-integer into the compact set
`(infinite box) × ∏_{v ∈ S_f} 𝒪_v`. -/
lemma exists_translate (z : SAdeleRing F Sf) :
    ∃ ξ : F, ξ ∈ SIntegers Sf ∧
      (sDiagonal Sf ξ + z).1 ∈ AdelicBox.infiniteBox F ∧
      ∀ v : Sf, (sDiagonal Sf ξ + z).2 v ∈
        (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  classical
  let f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
    fun v => if h : v ∈ Sf then z.2 ⟨v, h⟩ else 0
  have hf : ∀ᶠ v in Filter.cofinite, f v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    refine (Sf.finite_toSet.eventually_cofinite_notMem).mono fun v hv => ?_
    simp only [f, dif_neg (show v ∉ Sf from hv)]
    exact zero_mem _
  let y : FiniteAdeleRing (𝓞 F) F := RestrictedProduct.mk f hf
  have hy : ∀ v, y v = f v := fun v => rfl
  obtain ⟨k, hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F y
  obtain ⟨o, ho, -⟩ := AdelicBox.existsUnique_int_add_mem_infiniteBox F
    (algebraMap F (InfiniteAdeleRing F) k + z.1)
  have hkv : ∀ v, algebraMap F (v.adicCompletion F) k + f v ∈ v.adicCompletionIntegers F := by
    intro v
    have := hk v
    rwa [AdelicBox.algebraMap_add_apply, hy] at this
  have hov : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) (o : F) ∈ v.adicCompletionIntegers F :=
    fun v => AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 F) F v o
  refine ⟨(o : F) + k, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ∉ Sf := by simpa using hv
    have h1 := hkv v
    simp only [f, dif_neg hv', add_zero] at h1
    rw [← algebraMap_mem_iff, map_add]
    exact add_mem (hov v) h1
  · have : (sDiagonal Sf ((o : F) + k) + z).1 =
        algebraMap F (InfiniteAdeleRing F) (o : F) + (algebraMap F (InfiniteAdeleRing F) k + z.1) := by
      rw [map_add, Prod.fst_add, Prod.fst_add, add_assoc]; rfl
    rw [this]; exact ho
  · intro v
    have h1 := hkv v
    simp only [f, dif_pos v.2] at h1
    have : (sDiagonal Sf ((o : F) + k) + z).2 v =
        algebraMap F (v.1.adicCompletion F) (o : F) +
          (algebraMap F (v.1.adicCompletion F) k + z.2 v) := by
      rw [map_add, Prod.snd_add, Prod.snd_add, Pi.add_apply, Pi.add_apply, add_assoc]; rfl
    rw [this]
    exact add_mem (hov v.1) h1

lemma discrete : DiscreteTopology (sIntegerLattice Sf) := by
  obtain ⟨U, hU, ⟨u, hu⟩, hsub⟩ := exists_isOpen_subset_infiniteBox (F := F)
  rw [discreteTopology_iff_isOpen_singleton_zero]
  let O : Set (SAdeleRing F Sf) := {x | x.1 + u ∈ U ∧
    ∀ v : Sf, x.2 v ∈ ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
      Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))}
  have hO : IsOpen O := by
    refine (hU.preimage (continuous_fst.add continuous_const)).inter ?_
    have h2 : IsOpen (⋂ v : Sf, (fun x : SAdeleRing F Sf => x.2 v) ⁻¹'
          ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
            Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))) :=
      isOpen_iInter_of_finite fun v =>
        (Valued.isOpen_valuationSubring _).preimage ((continuous_apply v).comp continuous_snd)
    convert h2 using 1
    ext x; rw [Set.mem_iInter]; exact Iff.rfl
  have he : ((↑) : sIntegerLattice Sf → SAdeleRing F Sf) ⁻¹' O = {0} := by
    ext z
    obtain ⟨x, hx⟩ := z
    obtain ⟨ξ, hξ, rfl⟩ := (mem_lattice Sf).1 hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hint : ξ ∈ (algebraMap (𝓞 F) F).range := by
        apply HeightOneSpectrum.mem_integers_of_valuation_le_one
        intro v
        by_cases hv : v ∈ Sf
        · exact (algebraMap_mem_iff v ξ).1 (h2 ⟨v, hv⟩)
        · exact hξ v (by simpa using hv)
      obtain ⟨o, rfl⟩ := hint
      obtain ⟨o', -, huniq⟩ := AdelicBox.existsUnique_int_add_mem_infiniteBox F u
      have h0 : (0 : 𝓞 F) = o' := huniq 0 (by simpa using hsub hu)
      have h1' : o = o' := huniq o (hsub h1)
      apply Subtype.ext
      show sDiagonal Sf (algebraMap (𝓞 F) F o) = 0
      rw [h1', ← h0, map_zero, map_zero]
    · intro h
      have h' : sDiagonal Sf ξ = 0 := congrArg Subtype.val h
      show (sDiagonal Sf ξ).1 + u ∈ U ∧ _
      rw [h']
      exact ⟨by simpa using hu, fun v => zero_mem _⟩
  rw [← he]
  exact hO.preimage continuous_subtype_val

lemma compact : CompactSpace (SAdeleRing F Sf ⧸ sIntegerLattice Sf) := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_infiniteBox_subset F
  let K : Set (SAdeleRing F Sf) := C ×ˢ (Set.pi Set.univ fun v : Sf =>
    ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
      Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))
  have hK : IsCompact K := by
    refine hC.prod (isCompact_univ_pi fun v => ?_)
    haveI : CompactSpace ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) :=
      inferInstance
    exact isCompact_iff_compactSpace.mpr this
  have hcover : (QuotientAddGroup.mk : SAdeleRing F Sf → SAdeleRing F Sf ⧸ sIntegerLattice Sf) '' K
      = Set.univ := by
    refine Set.eq_univ_of_forall fun q => QuotientAddGroup.induction_on q fun z => ?_
    obtain ⟨ξ, hξ, h1, h2⟩ := exists_translate Sf z
    refine ⟨sDiagonal Sf ξ + z, ⟨hsub h1, fun v _ => h2 v⟩, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact (mem_lattice Sf).2 ⟨ξ, hξ, by abel⟩
  exact isCompact_univ_iff.mp (hcover ▸ hK.image QuotientAddGroup.continuous_mk)

lemma natCast_mul_inv (n : ℕ) (hn : 0 < n) :
    (n : SAdeleRing F Sf) * sDiagonal Sf (n : F)⁻¹ = 1 := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← map_natCast (sDiagonal Sf) n, ← map_mul, mul_inv_cancel₀ hnF, map_one]

lemma divisible (n : ℕ) (hn : 0 < n) : Function.Surjective
    (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨((sDiagonal Sf (n : F)⁻¹ * a : SAdeleRing F Sf) : SAdeleRing F Sf ⧸ sIntegerLattice Sf), ?_⟩
  show n • (QuotientAddGroup.mk (sDiagonal Sf (n : F)⁻¹ * a) : SAdeleRing F Sf ⧸ sIntegerLattice Sf)
    = QuotientAddGroup.mk a
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, ← mul_assoc, natCast_mul_inv Sf n hn, one_mul]

lemma injective_iff (n : ℕ) (hn : 0 < n) : Function.Injective
    (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x) ↔ ((n : F)⁻¹ ∈ SIntegers Sf) := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · intro hinj
    have h1 : n • (QuotientAddGroup.mk (sDiagonal Sf (n : F)⁻¹) : SAdeleRing F Sf ⧸ sIntegerLattice Sf)
        = n • (0 : SAdeleRing F Sf ⧸ sIntegerLattice Sf) := by
      rw [smul_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, nsmul_eq_mul,
        natCast_mul_inv Sf n hn]
      exact (mem_lattice Sf).2 ⟨1, one_mem _, map_one _⟩
    have h2 := hinj h1
    rw [QuotientAddGroup.eq_zero_iff] at h2
    obtain ⟨s, hs, hseq⟩ := (mem_lattice Sf).1 h2
    rwa [(sDiagonal Sf).injective hseq] at hs
  · intro hinv x y hxy
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hab : (QuotientAddGroup.mk (n • a) : SAdeleRing F Sf ⧸ sIntegerLattice Sf) =
        QuotientAddGroup.mk (n • b) := by
      simpa only [QuotientAddGroup.mk_nsmul] using hxy
    obtain ⟨η, hη, hηeq⟩ := (mem_lattice Sf).1 (QuotientAddGroup.eq_iff_sub_mem.mp hab)
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine (mem_lattice Sf).2 ⟨(n : F)⁻¹ * η, mul_mem hinv hη, ?_⟩
    rw [map_mul, hηeq, ← nsmul_sub, nsmul_eq_mul, ← mul_assoc, mul_comm (sDiagonal Sf _),
      natCast_mul_inv Sf n hn, one_mul]

end SAdeleQuotientProof

open SAdeleQuotientProof

theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ A : Set F, A ⊆ (SIntegers Sf : Set F) → IsClosed (sDiagonal Sf '' A)) ∧
    DiscreteTopology (sIntegerLattice Sf) ∧
    CompactSpace (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    T2Space (SAdeleRing F Sf ⧸ sIntegerLattice Sf) ∧
    (∀ n : ℕ, 0 < n → Function.Surjective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x)) ∧
    (∀ n : ℕ, 0 < n → (Function.Injective
      (fun x : SAdeleRing F Sf ⧸ sIntegerLattice Sf => n • x) ↔
        ((n : F)⁻¹ ∈ SIntegers Sf))) := by
  letI hd : DiscreteTopology (sIntegerLattice Sf) := discrete Sf
  have hcl : IsClosed (sIntegerLattice Sf : Set (SAdeleRing F Sf)) := AddSubgroup.isClosed_of_discrete
  refine ⟨?_, hd, compact Sf, inferInstance, divisible Sf, injective_iff Sf⟩
  intro A hA
  exact isClosed_of_subset_discrete_closed
    (fun _ h => by obtain ⟨r, hr, rfl⟩ := h; exact (mem_lattice Sf).2 ⟨r, hA hr, rfl⟩)
    (isDiscrete_iff_discreteTopology.mpr hd) hcl
