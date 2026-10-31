-- Prove2me | solution 1 for OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:10:21.945826+00:00
-- url     : https://prove2.me/submissions/edd1f512-d868-4d44-a9ce-9430c31759aa

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K015
import Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_endpoint_of_rTilde_eq

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ModuleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Height-one membership into free targets, minimal covers, graded Nakayama, reverse projectivity, saturated edge kernels and strict Hilbert detection.
-/

section


/-! The local algebra step in `loc:decomposition`, source §4.4. The maps
are actual linear maps; neither a decomposition nor a lift is assumed. -/
namespace KLInvariance.LocalCover

variable {R B P N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

/-- A lift through a minimal free cover is automatically surjective. This
is the exact Nakayama step of plane-localized BMP decomposition. -/
theorem lift_surjective [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N) (g : B →ₗ[R] P)
    (hφ : Function.Surjective φ) (hg : π.comp g = φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    Function.Surjective g := by
  apply LinearMap.surjective_of_surjective_comp_mkQ g (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro q
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨b, hb⟩ := hφ (π p)
  refine ⟨b, ?_⟩
  change Submodule.Quotient.mk (g b) = Submodule.Quotient.mk p
  apply (Submodule.Quotient.eq _).mpr
  apply hmin
  change π (g b - p) = 0
  rw [map_sub, ← LinearMap.comp_apply, hg, hb, sub_self]

/-- The full minimal-cover splitting required at each descending vertex.
The new kernel is proved finite free over the local ring, not introduced
as a free summand hypothesis. -/
theorem exists_split_minimal_cover [Module.Free R B] [Module.Finite R B]
    [Module.Free R P] [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N)
    (hπ : Function.Surjective π) (hφ : Function.Surjective φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    ∃ (g : B →ₗ[R] P) (e : B ≃ₗ[R] P × LinearMap.ker g),
      Function.Surjective g ∧ π.comp g = φ ∧
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ b, (e b).1 = g b ∧ π (e b).1 = φ b := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π φ hπ
  have hsurj := lift_surjective π φ g hφ hg hmin
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let e := splitEquiv g s hs
  let k : B →ₗ[R] LinearMap.ker g := (LinearMap.snd R P (LinearMap.ker g)).comp e.toLinearMap
  have hk : Function.Surjective k := by
    intro b
    exact ⟨e.symm (0, b), by simp [k]⟩
  have hki : k.comp (LinearMap.ker g).subtype = LinearMap.id := by
    ext b
    change ((b : B) - s (g b)) = b
    simp []
  let : Module.Finite R (LinearMap.ker g) := Module.Finite.of_surjective k hk
  let : Module.Projective R (LinearMap.ker g) :=
    Module.Projective.of_split (LinearMap.ker g).subtype k hki
  let : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
  refine ⟨g, e, hsurj, hg, inferInstance, inferInstance, ?_⟩
  intro b
  exact ⟨rfl, LinearMap.congr_fun hg b⟩

end KLInvariance.LocalCover


namespace KLInvariance.ReverseFiltration

variable {R F E I : Type*} [CommRing R]
  [AddCommGroup F] [Module R F] [AddCommGroup E] [Module R E]
  [AddCommGroup I] [Module R I]

/-- The kernel of a surjection from a projective module is projective if
the target has an actual length-one projective presentation. -/
theorem kernel_projective_of_presentation
    [Module.Projective R F] [Module.Projective R E]
    (f : F →ₗ[R] I) (g : E →ₗ[R] I)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R (LinearMap.ker g)] :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨a, ha⟩ := Module.projective_lifting_property g f hg
  obtain ⟨b, hb⟩ := Module.projective_lifting_property f g hf
  have ha' (x : F) : g (a x) = f x := LinearMap.congr_fun ha x
  have hb' (x : E) : f (b x) = g x := LinearMap.congr_fun hb x
  let a₀ : LinearMap.ker f →ₗ[R] LinearMap.ker g :=
    { toFun := fun x => ⟨a x, by simp [LinearMap.mem_ker, ha']⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun r x => Subtype.ext (by simp) }
  let i : LinearMap.ker f →ₗ[R] F × LinearMap.ker g :=
    (LinearMap.ker f).subtype.prod a₀
  let r : F × LinearMap.ker g →ₗ[R] LinearMap.ker f :=
    { toFun := fun x => ⟨x.1 - b (a x.1) + b x.2, by
        simp [LinearMap.mem_ker, hb', ha']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_add, smul_sub]) }
  apply Module.Projective.of_split i r
  ext x
  change (x : F) - b (a x) + b (a x) = x
  exact sub_add_cancel _ _

end KLInvariance.ReverseFiltration


end

section

namespace KLInvariance.Hilbert
universe uk um
variable {k : Type uk} {M : Type um} [Field k] [AddCommGroup M] [Module k M]

lemma piece_mono (𝓜 : ℤ → Submodule k M) {S T : Submodule k M}
    (h : S ≤ T) (n : ℤ) : piece 𝓜 S n ≤ piece 𝓜 T n :=
  Submodule.comap_mono h

lemma term_nonneg (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    {q : ℝ} (hq : 0 < q) (n : ℤ) : 0 ≤ term 𝓜 S q n := by
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos hq _))

lemma term_mono (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q) (n : ℤ) :
    term 𝓜 S q n ≤ term 𝓜 T q n := by
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos hq _))
  exact_mod_cast Submodule.finrank_mono (piece_mono 𝓜 h n)

lemma summable_of_le (𝓜 : ℤ → Submodule k M) [∀ n, Module.Finite k (𝓜 n)]
    {S T : Submodule k M} (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) : Summable (term 𝓜 S q) :=
  Summable.of_nonneg_of_le (term_nonneg 𝓜 S hq) (term_mono 𝓜 h hq) hT

/-- Equality at one positive convergent parameter, with actual inclusion,
forces equality of each homogeneous piece. -/
theorem pieces_eq_of_value_eq (𝓜 : ℤ → Submodule k M)
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) {q : ℝ} (hq : 0 < q)
    (hT : Summable (term 𝓜 T q)) (hv : value 𝓜 S q = value 𝓜 T q) :
    ∀ n, piece 𝓜 S n = piece 𝓜 T n := by
  intro n
  apply Submodule.eq_of_le_of_finrank_eq (piece_mono 𝓜 h n)
  by_contra hne
  have hlt : Module.finrank k (piece 𝓜 S n) < Module.finrank k (piece 𝓜 T n) :=
    lt_of_le_of_ne (Submodule.finrank_mono (piece_mono 𝓜 h n)) hne
  have hterm : term 𝓜 S q n < term 𝓜 T q n := by
    apply mul_lt_mul_of_pos_right _ (zpow_pos hq n)
    exact_mod_cast hlt
  have hstrict := (summable_of_le 𝓜 h hq hT).tsum_lt_tsum
    (term_mono 𝓜 h hq) hterm hT
  exact (ne_of_lt hstrict) hv

/-- No assumption on support codimension is involved. Equality of convergent
Hilbert values detects equality with a homogeneous target globally. -/
theorem eq_of_value_eq (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [∀ n, Module.Finite k (𝓜 n)] {S T : Submodule k M}
    (h : S ≤ T) (hhom : ∀ n m, m ∈ T → (DirectSum.decompose 𝓜 m n : M) ∈ T)
    {q : ℝ} (hq : 0 < q) (hT : Summable (term 𝓜 T q))
    (hv : value 𝓜 S q = value 𝓜 T q) : S = T := by
  classical
  apply le_antisymm h
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜 m]
  apply Submodule.sum_mem
  intro n hn
  have heq := pieces_eq_of_value_eq 𝓜 h hq hT hv n
  have hmem : DirectSum.decompose 𝓜 m n ∈ piece 𝓜 T n := hhom n m hm
  rw [←heq] at hmem
  exact hmem

end KLInvariance.Hilbert

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

attribute [local instance] OAI.KLInvariance.Dihedral.instDecidable_solutions
theorem eq_alt_of_descent (cs : CoxeterSystem M W) (i : Bool) {w : W}
    (h : cs.length (cs.simple i * w) < cs.length w) :
    w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced (cs.simple i * w)
  have hlen : cs.length w = ω.length + 1 := by
    have := cs.length_simple_mul w i
    rw [hw, hω.eq] at this h
    omega
  have hp : cs.wordProd (i :: ω) = w := by
    simp only [cs.wordProd_cons, ← hw, cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: ω) := by
    simpa only [CoxeterSystem.IsReduced, hp, List.length_cons] using hlen
  rw [hlen, ← reduced_cons_eq_alt cs i ω hr, hp]

end KLInvariance.Dihedral

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Tits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual Bruhat graph labels, Tits realizations and extended root spaces, cotangent coordinates and standard parabolic support.
-/

section

/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Two ambient vertices in a left coset of this plane subgroup can have
no reflection edge except one whose actual root is in the plane. -/
theorem reflection_between_coset_mem {P : Submodule ℝ (I → ℝ)} {t g h a : W}
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P)
    (heq : h*a=t*(g*a)) {r : I → ℝ} (ht : Represents M cs t r) : r ∈ P := by
  have htg : t*g=h := by apply mul_right_cancel (b := a); simpa only [mul_assoc] using heq.symm
  have htG : t ∈ planeSubgroup M cs P := by
    have heq' : t=h*g⁻¹ := by rw [← htg]; group
    rw [heq']
    exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
  exact (Represents.planeSubgroup_mem_iff M cs ht).mp htG

end
end KLInvariance.TitsSpace

/-! Construction of the source's geometric reflection schedule. The moment
curve avoids every forbidden hyperplane of a countable root set, using only
finite polynomial root sets and uncountability of the real field. -/

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_graded _root_.OAI.KLInvariance.TitsSpace.bottRealModule _root_.OAI.KLInvariance.TitsSpace.bottRealTower _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_decomposition _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_graded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_5
theorem planeRoot_ne (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : planeRoot x a P ≠ a :=
  (planeWeight_support_root x a P.val P.property).choose_spec.1

theorem planeRoot_plane (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : rootPlane a (planeRoot x a P) = P.val :=
  (planeWeight_support_root x a P.val P.property).choose_spec.2

theorem embed_not_rootLine (a b : PositiveRoot M cs) (hab : b ≠ a) :
    embed M b.val ∉ rootLine (k := ℝ) (embed M a.val) := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hli := (linearIndependent_fin2.mp (positiveRoots_independent b a hab)).2 c
  change c • a.val ≠ b.val at hli
  apply hli
  have hh := congrArg Prod.fst hc
  simpa only [embed,Prod.smul_fst] using hh


theorem edgeFactorDegree_cast (x : W) (a : PositiveRoot M cs) :
    (edgeFactorDegree x a : ℤ) = (planeWeight x a).sum (fun _ n => n) := by
  classical
  simp only [edgeFactorDegree,Nat.cast_sum]
  simp_rw [Int.toNat_of_nonneg (planeWeight_nonneg x a _)]
  exact Finset.sum_coe_sort (planeWeight x a).support (fun P => planeWeight x a P)


end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem reducedRoot_prime (a v : V) (hv : v ∉ rootLine (k := k) a) :
    Prime (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) := by
  apply (MulEquiv.prime_iff (rootQuotientEquiv (k := k) a)).mp
  rw [rootQuotientEquiv_mk_ι]
  apply symmetric_ι_prime
  intro h
  exact hv ((Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp h)

end
end KLInvariance.EdgeAlgebra

/-! NEW GRAPH CLOSURE -/


namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem two_step_rank_two (cs : CoxeterSystem M W) {x y : W}
    (hlen : cs.length y = cs.length x+2) :
    ∃ a b : W, a ≠ b ∧
      ∀ z, (BruhatStep cs x z ∧ BruhatStep cs z y) ↔ z=a ∨ z=b := by
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs (by omega : 0 < cs.length x+1)
    (w := y) (by omega)
  refine ⟨a,b,hab,?_⟩
  intro z
  rw [← hab',step_iff_odd,step_iff_odd]
  constructor
  · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
    omega
  · intro hz
    constructor <;> constructor
    · omega
    · rw [Nat.odd_iff]; omega
    · omega
    · rw [Nat.odd_iff]; omega

end KLInvariance.Dihedral

namespace KLInvariance
variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

namespace Dihedral
variable {M₂ : CoxeterMatrix Bool}

theorem two_interval_elements_length (cs : CoxeterSystem M₂ W)
    {u b : W} (x y : Interval cs u b) {n : ℕ}
    (hn₁ : cs.length x.val < n) (hn₂ : n < cs.length y.val) :
    ∃ a c : Interval cs u b, a ≠ c ∧ cs.length a.val=n ∧ cs.length c.val=n := by
  obtain ⟨a,c,hac,hlevel⟩ := two_elements_length cs (by omega : 0<n) hn₂
  have ha := (hlevel a).mpr (Or.inl rfl)
  have hc := (hlevel c).mpr (Or.inr rfl)
  have hmem (z : W) (hz : cs.length z=n) :
      BruhatLE cs u z ∧ BruhatLE cs z b :=
    ⟨bruhat_trans cs x.property.1 (shorter_bruhat cs (by omega)),
      bruhat_trans cs (shorter_bruhat cs (by omega)) y.property.2⟩
  exact ⟨⟨a,hmem a ha⟩,⟨c,hmem c hc⟩,
    fun he => hac (congrArg Subtype.val he),ha,hc⟩

end Dihedral
end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) (x : V)

namespace AboveIso
variable {B C x} (j : AboveIso B C x)

/-- One genuine descending splitting: the finite-free new top summand is
proved from the local-ring minimum cover, and all outgoing restriction maps
commute with the selected edge isomorphisms. -/
theorem extend_stalk [IsLocalRing R]
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)]
    [Module.Free R (C.vertex x)] [Module.Finite R (C.vertex x)]
    (hBf : B.Flabby) (hBg : B.Generated) (hCf : C.Flabby) (hCg : C.Generated)
    (hmin : LinearMap.ker (C.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x))) :
    ∃ (g : B.vertex x →ₗ[R] C.vertex x)
      (jv : B.vertex x ≃ₗ[R] C.vertex x × LinearMap.ker g),
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ (b : B.vertex x) (e : Outgoing (G := G) x),
        j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)) (B.stalkMap x b e) =
          C.stalkMap x (jv b).1 e := by
  let N := LinearMap.range (C.stalkMap x)
  let π : C.vertex x →ₗ[R] N := (C.stalkMap x).rangeRestrict
  have him := j.map_stalk_image hBf hBg hCf hCg
  let φ : B.vertex x →ₗ[R] N := LinearMap.codRestrict N
    (j.boundary.toLinearMap.comp (B.stalkMap x)) (by
      intro b
      change j.boundary (B.stalkMap x b) ∈ LinearMap.range (C.stalkMap x)
      rw [← him]
      exact ⟨B.stalkMap x b,⟨b,rfl⟩,rfl⟩)
  have hφ : Function.Surjective φ := by
    intro n
    have hn : n.val ∈ (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap := by
      rw [him]
      exact n.property
    rcases hn with ⟨w,⟨b,rfl⟩,hb⟩
    exact ⟨b,Subtype.ext hb⟩
  have hπmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x)) := by
    intro c hc
    apply hmin
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hc)
  obtain ⟨g,jv,_,hg,hfree,hfinite,hjv⟩ :=
    LocalCover.exists_split_minimal_cover π φ (by intro n; obtain ⟨c,hc⟩ := n.property; exact ⟨c,Subtype.ext hc⟩) hφ hπmin
  refine ⟨g,jv,hfree,hfinite,?_⟩
  intro b e
  have h := congrArg (fun n : N => n.val e) (hjv b).2
  exact h.symm

end AboveIso
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i}

lemma pi_compatible (B : ι → Sheaf.{u,v,w,z} (R := R) G) (Ω : Set V)
    (f : (pi B).Assignment) :
    (pi B).CompatibleOn Ω f ↔ ∀ i, (B i).CompatibleOn Ω (fun x => f x i) := by
  constructor
  · intro h i e hs ht
    exact congrFun (h e hs ht) i
  · intro h e hs ht
    funext i
    exact h i e hs ht

lemma pi_generated (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Generated) : (pi B).Generated := by
  intro x v
  classical
  choose f hf hfx using fun i => h i x (v i)
  exact ⟨fun y i => f i y,(pi_compatible B Set.univ _).mpr hf,funext hfx⟩

lemma pi_flabby (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Flabby) : (pi B).Flabby := by
  intro Ω hΩ f hf
  classical
  choose g hg hgf using fun i => h i Ω hΩ (fun x => f x i) ((pi_compatible B Ω f).mp hf i)
  exact ⟨fun y i => g i y,(pi_compatible B Set.univ _).mpr hg,fun x hx => funext (fun i => hgf i x hx)⟩

lemma pi_kernel_iff (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V)
    (f : (pi B).vertex x) :
    f ∈ LinearMap.ker ((pi B).stalkMap x) ↔ ∀ i, f i ∈ LinearMap.ker ((B i).stalkMap x) := by
  constructor
  · intro h i
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩) i
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e i
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (LinearMap.mem_ker.mp (h i)) ⟨e,rfl⟩

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i} [Fintype ι]

lemma pi_minimal (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (h : ∀ i, LinearMap.ker ((B i).stalkMap x) ≤ I • (⊤ : Submodule R ((B i).vertex x))) :
    LinearMap.ker ((pi B).stalkMap x) ≤ I • (⊤ : Submodule R ((pi B).vertex x)) := by
  intro f hf
  exact LocalCover.pi_mem_ideal_smul (fun i => (B i).vertex x) I f
    (fun i => h i ((pi_kernel_iff B x f).mp hf i))

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/

section

namespace KLInvariance.Hilbert

/-- Sum over all monomials in finitely many variables, before grouping by degree. -/
theorem hasSum_monomials (σ : Type*) [Fintype σ] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ) := by
  classical
  apply Fintype.induction_empty_option (P := fun σ _ =>
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ))
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Fintype.card_congr e]
    apply (Equiv.piCongrLeft (fun _ : β => ℕ) e).hasSum_iff.mp
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    simp only [Function.comp_apply, Equiv.piCongrLeft_apply]
    congr 1
    simpa using e.symm.sum_comp d
  · simp
  · intro α _ ih
    have hg := hasSum_geometric_of_lt_one hq hq1
    have hs := hg.summable.mul_of_nonneg ih.summable
      (fun _ => pow_nonneg hq _) (fun _ => pow_nonneg hq _)
    have hh := hg.mul ih hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hh
    simpa [Function.comp_def, Fintype.sum_option, pow_add, pow_succ, mul_comm] using he


lemma intWeight_eq_natWeight {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) d : ℕ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]

lemma polynomialGrading_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Graded.polynomialGrading k σ n =
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℕ)) n := by
  ext p
  change (∀ d, p.coeff d ≠ 0 →
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d = (n : ℤ)) ↔ _
  simp only [intWeight_eq_natWeight, Nat.cast_inj]
  rfl

instance polynomialPiece_finite (k : Type*) [Field k] (σ : Type*) [Finite σ] (n : ℤ) :
    Module.Finite k (Graded.polynomialGrading k σ n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polynomialGrading_nat]
    exact Module.Finite.iff_fg.mpr
      (MvPolynomial.weightedHomogeneousSubmodule_fg k (fun _ : σ => 1) (by simp) m)
  · rw [Graded.polynomialGrading_negative k σ n (lt_of_not_ge hn)]
    infer_instance

lemma polynomial_finrank_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Module.finrank k (Graded.polynomialGrading k σ n) =
      Nat.card {d : σ →₀ ℕ // Finsupp.weight (fun _ => (1 : ℕ)) d = n} := by
  rw [polynomialGrading_nat, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k _)

lemma hasSum_finsupp_monomials (σ : Type*) [Fintype σ] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ →₀ ℕ => q ^ Finsupp.weight (fun _ => (1 : ℕ)) d)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.mpr
    (hasSum_monomials σ hq hq1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  congr 1
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype d _ (by simp)

/-- The actual finite polynomial ring has Hilbert series `(1-q)⁻ᴺ`. -/
theorem hasSum_polynomial_nat (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (hasSum_finsupp_monomials σ hq hq1).tsum_fiberwise
    (Finsupp.weight (fun _ : σ => (1 : ℕ)))
  apply h.congr_fun
  intro n
  rw [polynomial_finrank_nat]
  have hf : (fun d : ↑((Finsupp.weight (R := ℕ) (fun _ : σ => (1 : ℕ))) ⁻¹' {n}) =>
      q ^ (Finsupp.weight (fun _ : σ => (1 : ℕ))) d.val) = fun _ => q^n := by
    funext d
    rw [show Finsupp.weight (fun _ : σ => (1 : ℕ)) d.val = n from d.property]
  rw [hf, tsum_const, nsmul_eq_mul]
  simp only [Set.preimage, Set.mem_singleton_iff]
  rfl


/-- Integer-indexed grading, including its zero negative pieces. -/
theorem hasSum_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  apply ((Nat.cast_injective : Function.Injective ((↑) : ℕ → ℤ)).hasSum_iff ?_).mp
  · simpa only [Function.comp_def, zpow_natCast] using hasSum_polynomial_nat k σ hq hq1
  · intro n hn
    have hn' : n < 0 := by
      by_contra h
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
      exact hn ⟨m, rfl⟩
    rw [Graded.polynomialGrading_negative k σ n hn']
    simp

end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

lemma shiftedPiece_finrank {ι : Type ui} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.finrank k (Graded.shiftedPiece 𝓐 d n) = ∑ i, Module.finrank k (𝓐 (n-d i)) := by
  rw [(shiftedPieceEquiv 𝓐 d n).finrank_eq, Module.finrank_pi_fintype]

lemma hasSum_shifted_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (d : ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ (n-d)) : ℝ) * q^n)
      (q^d * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  have h := (hasSum_polynomial k σ hq.le hq1).mul_left (q^d)
  apply h.congr_fun
  intro n
  change (Module.finrank k (Graded.polynomialGrading k σ (n+d-d)) : ℝ) * q^(n+d) = _
  rw [add_sub_cancel_right, zpow_add₀ hq.ne']
  ring

/-- Convergent Hilbert series and its normalization for the actual shifted free module. -/
theorem hasSum_shiftedFree (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {ι : Type*} [Fintype ι] (d : ι → ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ =>
      (Module.finrank k (Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) : ℝ) * q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  have h := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_shifted_polynomial k σ (d i) hq hq1)
  rw [← Finset.sum_mul] at h
  apply h.congr_fun
  intro n
  rw [shiftedPiece_finrank, Nat.cast_sum, Finset.sum_mul]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Any finite graded module admits a finite homogeneous free cover. No projectivity is assumed. -/
theorem exists_finite_graded_cover [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] :
    ∃ (ι : Type um), Finite ι ∧ ∃ (d : ι → ℤ) (f : (ι → A) →ₗ[A] M),
      Function.Surjective f ∧ ∀ n v, v ∈ Graded.shiftedPiece 𝓐 d n → f v ∈ 𝓜 n := by
  classical
  obtain ⟨t,ht,hd⟩ := Graded.exists_finite_homogeneous_generators (A := A) 𝓜
  choose d hd using fun i : t => hd i.val i.property
  have hspan : Submodule.span A (Set.range fun i : t => i.val) = ⊤ := by simpa using ht
  refine ⟨t, inferInstance, d, Fintype.linearCombination A (fun i : t => i.val), ?_, ?_⟩
  · intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  · intro n v hv
    change (∑ i, v i • (i : M)) ∈ 𝓜 n
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

lemma degreeMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) : Function.Surjective (degreeMap 𝓜 𝓝 f hf n) := by
  intro m
  obtain ⟨v,hv⟩ := hs m.val
  refine ⟨DirectSum.decompose 𝓜 v n, ?_⟩
  apply Subtype.ext
  change f (Graded.component 𝓜 n v) = m.val
  have h := Graded.map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero, hv] at h
  exact h.symm.trans (DirectSum.decompose_of_mem_same 𝓝 m.property)
end FiniteModule

lemma term_top {M : Type um} [AddCommGroup M] [Module k M]
    (𝓜 : ℤ → Submodule k M) (q : ℝ) (n : ℤ) :
    term 𝓜 ⊤ q n = (Module.finrank k (𝓜 n) : ℝ)*q^n := by
  rw [term, piece, Submodule.comap_top, finrank_top]

section PolynomialModule
variable (k : Type uk) [Field k] (σ : Type ua) [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] [Module.Finite (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]

include σ

/-- Finiteness of every genuine homogeneous piece, not an extra assumption on the Hilbert series. -/
theorem polynomialModule_piece_finite (n : ℤ) : Module.Finite k (𝓜 n) := by
  classical
  obtain ⟨ι,hι,d,f,hs,hf⟩ := exists_finite_graded_cover (Graded.polynomialGrading k σ) 𝓜
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  exact Module.Finite.of_surjective
    (degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜 f hf n)
    (degreeMap_surjective _ _ f hf hs n)

/-- Every finite graded module over the actual finite polynomial ring has a convergent
Hilbert series at every `0<q<1`, even when it is not free. -/
theorem summable_polynomialModule {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n) := by
  classical
  obtain ⟨ι,hι,d,f,hs,hf⟩ := exists_finite_graded_cover (Graded.polynomialGrading k σ) 𝓜
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  apply (hasSum_shiftedFree k σ d hq hq1).summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq.le _)
  · intro n
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
    exact_mod_cast LinearMap.finrank_le_finrank_of_surjective
      (degreeMap_surjective (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜 f hf hs n)

/-- Convergence for every submodule in the fixed finite graded ambient module. -/
theorem summable_term (S : Submodule k M) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (term 𝓜 S q) := by
  let : ∀ n, Module.Finite k (𝓜 n) := polynomialModule_piece_finite k σ 𝓜
  have heq : term 𝓜 ⊤ q = fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n :=
    funext (term_top 𝓜 q)
  have htop : Summable (term 𝓜 ⊤ q) := by
    rw [heq]
    exact summable_polynomialModule k σ 𝓜 hq hq1
  exact summable_of_le 𝓜 le_top hq htop

/-- Global detection, now with all the manuscript's finite-polynomial-ring hypotheses supplied. -/
theorem polynomial_eq_of_value_eq {S T : Submodule k M}
    (h : S ≤ T) (hhom : ∀ n m, m ∈ T → Graded.component 𝓜 n m ∈ T)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hv : value 𝓜 S q = value 𝓜 T q) : S = T := by
  let : ∀ n, Module.Finite k (𝓜 n) := polynomialModule_piece_finite k σ 𝓜
  exact eq_of_value_eq 𝓜 h hhom hq (summable_term k σ 𝓜 T hq hq1) hv
end PolynomialModule


end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 theorem finrank_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) :
    Module.finrank k (𝓜 n) = Module.finrank k (subPiece 𝓜 (LinearMap.ker f) n) +
      Module.finrank k (𝓝 n) := by
  have h := LinearMap.finrank_range_add_finrank_ker (degreeMap 𝓜 𝓝 f hf n)
  rw [LinearMap.range_eq_top.mpr (degreeMap_surjective 𝓜 𝓝 f hf hs n),finrank_top,
    ← (degreeKernelEquiv 𝓜 𝓝 f hf n).finrank_eq] at h
  omega


 theorem value_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (q : ℝ)
    (hK : Summable (term (subPiece 𝓜 (LinearMap.ker f)) ⊤ q))
    (hN : Summable (term 𝓝 ⊤ q)) :
    value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.ker f)) ⊤ q + value 𝓝 ⊤ q := by
  have ht : term 𝓜 ⊤ q = fun n => term (subPiece 𝓜 (LinearMap.ker f)) ⊤ q n +
      term 𝓝 ⊤ q n := by
    funext n
    rw [term_top,term_top,term_top,finrank_exact 𝓜 𝓝 f hf hs n,Nat.cast_add,add_mul]
  rw [value,ht,hK.tsum_add hN]
  rfl

/-- Finite degreewise exactness supplies convergence of both terms; no
free-module hypothesis is used. -/
 theorem value_exact_of_summable
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) {q : ℝ} (hq : 0 < q)
    (hM : Summable (term 𝓜 ⊤ q)) :
    value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.ker f)) ⊤ q + value 𝓝 ⊤ q := by
  apply value_exact 𝓜 𝓝 f hf hs q
  · apply hM.of_nonneg_of_le
    · intro n
      rw [term_top]
      positivity
    · intro n
      rw [term_top,term_top]
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
      exact_mod_cast (show Module.finrank k (subPiece 𝓜 (LinearMap.ker f) n) ≤
        Module.finrank k (𝓜 n) by rw [finrank_exact 𝓜 𝓝 f hf hs n]; omega)
  · apply hM.of_nonneg_of_le
    · intro n
      rw [term_top]
      positivity
    · intro n
      rw [term_top,term_top]
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
      exact_mod_cast (show Module.finrank k (𝓝 n) ≤ Module.finrank k (𝓜 n) by
        rw [finrank_exact 𝓜 𝓝 f hf hs n]; omega)

end KLInvariance.Hilbert

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 theorem term_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) (n : ℤ) :
    term (subPiece 𝓜 S) ⊤ q n = term 𝓜 (S.restrictScalars k) q n := by
  rw [term_top,term,(subPieceEquiv 𝓜 S n).finrank_eq]

 theorem value_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) :
    value (subPiece 𝓜 S) ⊤ q = value 𝓜 (S.restrictScalars k) q := by
  exact tsum_congr (term_subPiece 𝓜 S q)

 theorem imagePieceMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    Function.Surjective (imagePieceMap 𝓜 𝓝 S f hf n) := by
  rintro ⟨⟨m,hm⟩,hgrad⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  refine ⟨⟨⟨component 𝓜 n v,hS n v hv⟩,(DirectSum.decompose 𝓜 v n).property⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (component 𝓜 n v) = f v
  have hh := map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero] at hh
  rw [← hh]
  exact DirectSum.decompose_of_mem_same 𝓝 hgrad

 theorem finrank_image_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    Module.finrank k (piece 𝓜 (S.restrictScalars k) n) =
      Module.finrank k (piece 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) n) +
      Module.finrank k (piece 𝓝 ((S.map f).restrictScalars k) n) := by
  let : Module.Finite k (subPiece 𝓜 S n) := Module.Finite.of_surjective
    (subPieceEquiv 𝓜 S n).symm.toLinearMap (subPieceEquiv 𝓜 S n).symm.surjective
  have h := LinearMap.finrank_range_add_finrank_ker (imagePieceMap 𝓜 𝓝 S f hf n)
  rw [LinearMap.range_eq_top.mpr (imagePieceMap_surjective 𝓜 𝓝 S hS f hf n),finrank_top,
    ← (imageKernelEquiv 𝓜 𝓝 S f hf n).finrank_eq,
    (subPieceEquiv 𝓜 S n).finrank_eq,
    (subPieceEquiv 𝓜 (S ⊓ LinearMap.ker f) n).finrank_eq,
    (subPieceEquiv 𝓝 (S.map f) n).finrank_eq] at h
  omega

/-- Removing a kernel condition adds exactly the Hilbert value of its
embedded restriction image. No freeness of the source kernel is used. -/
 theorem value_image_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    {q : ℝ} (hq : 0 < q) (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓜 (S.restrictScalars k) q =
      value 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q +
      value 𝓝 ((S.map f).restrictScalars k) q := by
  have ht (n : ℤ) : term 𝓜 (S.restrictScalars k) q n =
      term 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q n +
      term 𝓝 ((S.map f).restrictScalars k) q n := by
    unfold term
    rw [finrank_image_exact 𝓜 𝓝 S hS f hf n,Nat.cast_add,add_mul]
  have hk : Summable (term 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q) := by
    apply hs.of_nonneg_of_le
    · exact fun n => term_nonneg _ _ hq n
    · intro n
      rw [ht n]
      exact le_add_of_nonneg_right (term_nonneg _ _ hq n)
  have hi : Summable (term 𝓝 ((S.map f).restrictScalars k) q) := by
    apply hs.of_nonneg_of_le
    · exact fun n => term_nonneg _ _ hq n
    · intro n
      rw [ht n]
      exact le_add_of_nonneg_left (term_nonneg _ _ hq n)
  unfold value
  rw [show term 𝓜 (S.restrictScalars k) q = _ from funext ht,hk.tsum_add hi]

end KLInvariance.Hilbert

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/

section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

 theorem upwardKernel_insert (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x) :
    B.upwardSubmodule x (insert e F) =
      B.upwardSubmodule x F ⊓ LinearMap.ker (B.lowerAt x e).map := by
  ext v
  change (∀ a ∈ insert e F, B.forget.stalkMap x v a = 0) ↔
    (∀ a ∈ F, B.forget.stalkMap x v a = 0) ∧ (B.lowerAt x e).map v = 0
  rw [B.lowerAt_map]
  simp only [Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm


 theorem hilbert_edge_increment
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x)
    [∀ n, Module.Finite k ((B.vertex x).piece n)]
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex x).piece
      ((B.upwardSubmodule x F).restrictScalars k) q)) :
    value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars k) q =
      value (B.vertex x).piece
        ((B.upwardSubmodule x (insert e F)).restrictScalars k) q +
      value (B.edge e.val).piece
        (((B.upwardSubmodule x F).map (B.lowerAt x e).map).restrictScalars k) q := by
  rw [B.upwardKernel_insert]
  exact value_image_exact (B.vertex x).piece (B.edge e.val).piece
    (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)
    (B.lowerAt x e).map (B.lowerAt x e).graded hq hs

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

lemma prod_generated (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Generated) (hC : C.Generated) : (prod B C).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hB x v.1
  obtain ⟨g,hg,hgx⟩ := hC x v.2
  exact ⟨fun y => (f y,g y),fun e hs ht => Prod.ext (hf e hs ht) (hg e hs ht),Prod.ext hfx hgx⟩

lemma prod_flabby (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Flabby) (hC : C.Flabby) : (prod B C).Flabby := by
  intro U hU f hf
  obtain ⟨g,hg,hgf⟩ := hB U hU (fun y => (f y).1) (fun e hs ht => congrArg Prod.fst (hf e hs ht))
  obtain ⟨t,ht,htf⟩ := hC U hU (fun y => (f y).2) (fun e hs htt => congrArg Prod.snd (hf e hs htt))
  exact ⟨fun y => (g y,t y),fun e hs htt => Prod.ext (hg e hs htt) (ht e hs htt),
    fun y hy => Prod.ext (hgf y hy) (htf y hy)⟩

lemma prod_upperQuotient (B C : Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) : (prod B C).UpperQuotient α := by
  intro e
  refine ⟨?_,?_⟩
  · intro v
    obtain ⟨b,hb⟩ := (hB e).1 v.1
    obtain ⟨c,hc⟩ := (hC e).1 v.2
    exact ⟨(b,c),Prod.ext hb hc⟩
  · intro v
    constructor
    · intro h
      obtain ⟨b,hb⟩ := (hB e).2 v.1 |>.mp (congrArg Prod.fst h)
      obtain ⟨c,hc⟩ := (hC e).2 v.2 |>.mp (congrArg Prod.snd h)
      exact ⟨(b,c),Prod.ext hb hc⟩
    · rintro ⟨⟨b,c⟩,rfl⟩
      exact Prod.ext ((hB e).2 _ |>.mpr ⟨b,rfl⟩) ((hC e).2 _ |>.mpr ⟨c,rfl⟩)

lemma pi_upperQuotient {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : ∀ i, (B i).UpperQuotient α) : (pi B).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose b hb using fun i => (hB i e).1 (v i)
    exact ⟨b,funext hb⟩
  · intro v
    constructor
    · intro h
      choose b hb using fun i => (hB i e).2 (v i) |>.mp (congrFun h i)
      exact ⟨b,funext hb⟩
    · rintro ⟨b,rfl⟩
      funext i
      exact (hB i e).2 _ |>.mpr ⟨b i,rfl⟩

lemma prod_kernel_iff (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (v : (prod B C).vertex x) :
    v ∈ LinearMap.ker ((prod B C).stalkMap x) ↔
      v.1 ∈ LinearMap.ker (B.stalkMap x) ∧ v.2 ∈ LinearMap.ker (C.stalkMap x) := by
  constructor
  · intro h
    constructor <;> apply LinearMap.mem_ker.mpr <;> funext e
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.fst (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.snd (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
  · rintro ⟨hB,hC⟩
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact Prod.ext (congrFun (LinearMap.mem_ker.mp hB) ⟨e,rfl⟩)
      (congrFun (LinearMap.mem_ker.mp hC) ⟨e,rfl⟩)

lemma prod_minimal (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (hB : LinearMap.ker (B.stalkMap x) ≤ I • (⊤ : Submodule R (B.vertex x)))
    (hC : LinearMap.ker (C.stalkMap x) ≤ I • (⊤ : Submodule R (C.vertex x))) :
    LinearMap.ker ((prod B C).stalkMap x) ≤ I • (⊤ : Submodule R ((prod B C).vertex x)) := by
  intro v hv
  obtain ⟨hvB,hvC⟩ := (prod_kernel_iff B C x v).mp hv
  have h (M N : Type z) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (f : M →ₗ[R] N) : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hb := h _ _ (LinearMap.inl R (B.vertex x) (C.vertex x)) ⟨v.1,hB hvB,rfl⟩
  have hc := h _ _ (LinearMap.inr R (B.vertex x) (C.vertex x)) ⟨v.2,hC hvC,rfl⟩
  have heq : (v.1,0) + (0,v.2) = v := Prod.ext (add_zero _) (zero_add _)
  have hh := (I • (⊤ : Submodule R ((prod B C).vertex x))).add_mem hb hc
  change (v.1,0) + (0,v.2) ∈ I • (⊤ : Submodule R ((prod B C).vertex x)) at hh
  exact heq ▸ hh

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  {B C : Sheaf.{u,v,w,z} (R := R) G} (D : Sheaf.{u,v,w,z} (R := R) G)

lemma pi_subsingleton_vertex {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (x : V) (h : ∀ i, Subsingleton ((B i).vertex x)) : Subsingleton ((pi B).vertex x) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

lemma pi_subsingleton_edge {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (e : E) (h : ∀ i, Subsingleton ((B i).edge e)) : Subsingleton ((pi B).edge e) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

theorem baseChange_generated (h : B.Generated) : (B.baseChange S).Generated := by
  intro x v
  induction v using OAI.tensorInductionOn with
  | tmul s v =>
    obtain ⟨f,hf,hx⟩ := h x v
    exact ⟨fun y => s ⊗ₜ f y,B.baseChange_tmul_compatible S Set.univ s f hf,congrArg (fun v => s ⊗ₜ[R] v) hx⟩
  | add v w hv hw =>
    obtain ⟨f,hf,hfv⟩ := hv
    obtain ⟨g,hg,hgw⟩ := hw
    exact ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,congrArg₂ (·+·) hfv hgw⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem baseChange_vertex_free (x : V) [Module.Free R (B.vertex x)] :
    Module.Free S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Free S (S ⊗[R] B.vertex x))

 theorem baseChange_vertex_finite (x : V) [Module.Finite R (B.vertex x)] :
    Module.Finite S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Finite S (S ⊗[R] B.vertex x))

 theorem baseChange_upperQuotient [Module.Flat R S] (α : E → R)
    (h : B.UpperQuotient α) : (B.baseChange S).UpperQuotient (fun e => algebraMap R S (α e)) := by
  intro e
  refine ⟨LinearMap.lTensor_surjective S (h e).1, ?_⟩
  have hs : Function.Exact (DistribSMul.toLinearMap R (B.vertex (G.target e)) (α e))
      (B.upper e) := by
    intro v
    exact ((h e).2 v).trans (by simp only [Set.mem_range, DistribSMul.toLinearMap_apply,
      eq_comm])
  have ht := Module.Flat.lTensor_exact S hs
  intro v
  change (B.upper e).lTensor S v = 0 ↔ ∃ w, v = algebraMap R S (α e) • w
  rw [ht v, LinearMap.lTensor_smul_action]
  change (∃ w : S ⊗[R] B.vertex (G.target e), α e • w = v) ↔
    ∃ w : S ⊗[R] B.vertex (G.target e), v = algebraMap R S (α e) • w
  simp only [IsScalarTower.algebraMap_smul]
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem simpleRoot_mem (i : Bool) : (B.simpleRoot i).val ∈ P := by
  cases i
  · exact B.left_mem
  · exact B.right_mem

end PlaneBasis


end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine Bott--Samelson stalk Hilbert coefficients satisfy the simple
reflection ascent recurrence. Both exactness and the degree-one kernel shift
were constructed integrally above; no KL character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)

include ha in
 theorem scalar_value
    (hinj : Function.Injective (fun m : M => a • m)) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 ⊤ q)) :
    value (subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q =
      q^d * value 𝓜 ⊤ q := by
  have h := (hs.hasSum.mul_left (q^d))
  have hh : HasSum
      (fun n : ℤ => (Module.finrank k (𝓜 (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 ⊤ q) := by
    apply (Equiv.addRight d).hasSum_iff.mp
    apply h.congr_fun
    intro n
    rw [term_top]
    change (Module.finrank k (𝓜 (n+d-d)) : ℝ)*q^(n+d) =
      q^d * ((Module.finrank k (𝓜 n) : ℝ)*q^n)
    rw [add_sub_cancel_right,zpow_add₀ hq]
    ring
  apply HasSum.tsum_eq
  apply hh.congr_fun
  intro n
  rw [term_top,← LinearEquiv.finrank_eq (scalarDegreeEquiv 𝓐 𝓜 a d ha hinj n)]

end KLInvariance.Hilbert

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 theorem imageMap_surjective (S : Submodule A M) (f : M →ₗ[A] N) :
    Function.Surjective (imageMap S f) := by
  rintro ⟨m,hm⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  exact ⟨⟨v,hv⟩,rfl⟩

 theorem imageMap_ker (S : Submodule A M) (f : M →ₗ[A] N) (a : A)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hS : ∀ v, a • v ∈ S → v ∈ S) :
    LinearMap.ker (imageMap S f) = LinearMap.range (LinearMap.lsmul A S a) := by
  ext v
  constructor
  · intro hv
    have hz : f v.val = 0 := congrArg Subtype.val hv
    obtain ⟨w,hw⟩ := (hf v.val).mp hz
    have hwS : w ∈ S := hS w (hw ▸ v.property)
    exact ⟨⟨w,hwS⟩,Subtype.ext hw.symm⟩
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    exact (hf (a • w.val)).mpr ⟨w.val,rfl⟩

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨component 𝓜 n w,hS n w hw,?_⟩
  simpa using (map_component 𝓜 𝓝 f 0 (by simpa using hf) n w).symm

/-- The actual upper image of a saturated graded submodule has precisely
`(1-q^d)` times its Hilbert series. No choice of edge basis enters this identity. -/
theorem saturated_image_value
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)
    (hk : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ S → v ∈ S)
    (hinj : Function.Injective (fun v : M => a • v))
    {q : ℝ} (hq : 0 < q) (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      (1-q^d) * value 𝓜 (S.restrictScalars k) q := by
  let : DirectSum.Decomposition (subPiece 𝓜 S) := (sub_isInternal 𝓜 S hS).chooseDecomposition
  let : DirectSum.Decomposition (subPiece 𝓝 (S.map f)) :=
    (sub_isInternal 𝓝 (S.map f) (map_homogeneous 𝓜 𝓝 S hS f hf)).chooseDecomposition
  let (n : ℤ) : Module.Finite k (subPiece 𝓜 S n) := Module.Finite.of_surjective
    (subPieceEquiv 𝓜 S n).symm.toLinearMap (subPieceEquiv 𝓜 S n).symm.surjective
  have hs' : Summable (term (subPiece 𝓜 S) ⊤ q) :=
    hs.congr (fun n => (term_subPiece 𝓜 S q n).symm)
  have h := value_exact_of_summable (subPiece 𝓜 S) (subPiece 𝓝 (S.map f))
    (imageMap S f) (fun n v hv => hf n v.val hv) (imageMap_surjective S f) hq hs'
  rw [imageMap_ker S f a hk hsat] at h
  have hinj' : Function.Injective (fun v : S => a • v) := by
    intro v w hv
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hv
  rw [scalar_value 𝓐 (subPiece 𝓜 S) a d ha hinj' hq.ne' hs',
    value_subPiece,value_subPiece] at h
  linarith

end KLInvariance.Hilbert

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

 theorem upwardSubmodule_saturated (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (a : A) (hreg : ∀ e ∈ F, Function.Injective (fun v : B.edge e.val => a • v)) :
    ∀ v, a • v ∈ B.upwardSubmodule x F → v ∈ B.upwardSubmodule x F := by
  intro v hv e he
  have hz : (B.lowerAt x e).map (a • v) = 0 :=
    (B.lowerAt_map x e (a • v)).trans (hv e he)
  have hz' : (B.lowerAt x e).map v = 0 := by
    apply hreg e he
    change a • (B.lowerAt x e).map v = a • (0 : B.edge e.val)
    simpa only [map_smul,smul_zero] using hz
  exact (B.lowerAt_map x e v).symm.trans hz'


 theorem upper_image_value (α : E → A) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e)))
    [∀ n, Module.Finite k ((B.vertex (G.target e)).piece n)]
    (ha : α e ∈ 𝓐 1)
    (hreg : ∀ f ∈ F, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex (G.target e)).piece
      ((B.upwardSubmodule (G.target e) F).restrictScalars k) q)) :
    value (B.edge e).piece
        (((B.upwardSubmodule (G.target e) F).map (B.upper e).map).restrictScalars k) q =
      (1-q) * value (B.vertex (G.target e)).piece
        ((B.upwardSubmodule (G.target e) F).restrictScalars k) q := by
  simpa only [zpow_one] using saturated_image_value 𝓐
    (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) F) (B.upwardKernel_homogeneous (G.target e) F)
    (B.upper e).map (B.upper e).graded (α e) 1 ha (hquot e).2
    (B.upwardSubmodule_saturated (G.target e) F (α e) hreg) hinj hq hs

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem label_regular_stalk (e : Edge cs u b) (x : Interval cs u b) :
    Function.Injective (fun v : B.sheaf.vertex x => polynomialLabel cs u b basis e • v) := by
  let := B.free x
  exact smul_right_injective _ (polynomialLabel_ne_zero cs u b basis e)

omit [Fintype σ] in


 theorem incoming_label_regular_outgoing (e f : Edge cs u b)
    (h : (graph cs u b).source f = (graph cs u b).target e) :
    Function.Injective (fun v : B.sheaf.edge f => polynomialLabel cs u b basis e • v) := by
  let := B.free ((graph cs u b).target f)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target f)))
    (B.sheaf.upper f).map (B.quotient f).1
    (polynomialLabel cs u b basis f) (polynomialLabel cs u b basis e)
    (polynomialLabel_prime cs u b basis f)
    (outgoing_incoming_not_dvd cs u b basis _ f e h rfl) (B.quotient f).2

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! The finite sums used by the actual local decomposition. The model criteria
are kept explicit here; they are not asserted for the constructed BMP object
or inserted into the main KL theorem. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}


namespace ModelSum
variable {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {U : Set V} {B : Sheaf.{u,v,w,z} (R := R) G}

omit [IsLocalRing R] in
lemma mono {O : V → Sheaf.{u,v,w,z} (R := R) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n ih => exact .add ih c (hUT hc) n

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Free R (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma finite (h : ModelSum O.sheaf U B) (x : V) : Module.Finite R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Finite R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Finite R (C.vertex x) := ih
    let _ := O.finite c x
    change Module.Finite R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | add _ c _ n ih => exact prod_upperQuotient _ _ α ih (pi_upperQuotient _ α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.Generated := by
  induction h with
  | zero => exact fun x v => ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n ih => exact prod_generated _ _ ih (pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n ih => exact prod_flabby _ _ ih (pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) :
    LinearMap.ker (B.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (B.vertex x)) := by
  induction h with
  | zero =>
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | add _ c hc n ih =>
    exact prod_minimal _ _ x _ ih (pi_minimal _ x _
      (fun _ => O.minimal c x (fun he => hx (he ▸ hc))))

end ModelSum
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue uz
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

theorem scaledImages_iff (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    B.ScaledImages e F H r ↔
      (B.upwardKernel (G.source e) F).map (B.lower e) =
        r • (B.upwardKernel (G.target e) H).map (B.upper e) := by
  constructor
  · intro h
    ext z
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change (∃ v, v ∈ B.upwardKernel (G.source e) F ∧ B.lower e v=z) ↔ _
    rw [h z]
    constructor
    · rintro ⟨w,hw,he⟩
      exact ⟨B.upper e w,⟨w,hw,rfl⟩,he⟩
    · rintro ⟨t,⟨w,hw,rfl⟩,he⟩
      exact ⟨w,hw,he⟩
  · intro h z
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv' : B.lower e v ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        h ▸ (show B.lower e v ∈ (B.upwardKernel (G.source e) F).map (B.lower e) from ⟨v,hv,rfl⟩)
      obtain ⟨t,⟨w,hw,rfl⟩,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv'
      exact ⟨w,hw,he⟩
    · rintro ⟨w,hw,rfl⟩
      have hw' : r • B.upper e w ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨B.upper e w,⟨w,hw,rfl⟩,rfl⟩
      rw [← h] at hw'
      exact hw'

theorem prod_scaledImages (B C : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : B.ScaledImages e F H r) (hC : C.ScaledImages e F H r) :
    (prod B C).ScaledImages e F H r := by
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ F v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mp ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mp ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ H _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ H v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mpr ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mpr ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ F _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩

theorem pi_scaledImages {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : ∀ i, (B i).ScaledImages e F H r) : (pi B).ScaledImages e F H r := by
  classical
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ F v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mp ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ H _).mpr hw,funext hwe⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ H v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mpr ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ F _).mpr hw,funext hwe⟩

theorem zero_scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    (zero : Sheaf.{ur,uv,ue,uz} (R := R) G).ScaledImages e F H r := by
  intro z
  constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

theorem ModelSum.scaledImages {O : V → Sheaf.{ur,uv,ue,uz} (R := R) G}
    {U : Set V} {B : Sheaf.{ur,uv,ue,uz} (R := R) G} (h : ModelSum O U B)
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hO : ∀ c ∈ U, (O c).ScaledImages e F H r) : B.ScaledImages e F H r := by
  induction h with
  | zero => exact zero_scaledImages e F H r
  | add _ c hc n ih =>
    exact prod_scaledImages _ _ e F H r ih
      (pi_scaledImages (fun _ : Fin n => O c) e F H r (fun _ => hO c hc))

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem graphRoot_mem {a₀ : W} {g h : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀)) :
    (graphRoot he).val ∈ P := by
  exact reflection_between_coset_mem M cs (a := a₀) g.property h.property (by group)
    (graphRoot_represents he)

include B

/-- The two labels on a composable coset path span the whole actual plane. -/
theorem graphRoot_path_plane {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀)) :
    rootPlane (graphRoot he) (graphRoot hf) = P := by
  exact (rootPlane_eq_of_mem B.left B.right (graphRoot he) (graphRoot hf)
    B.distinct (B.plane_eq.ge (graphRoot_mem he)) (B.plane_eq.ge (graphRoot_mem hf))
    (graphRoot_ne_of_path he hf)).trans B.plane_eq


theorem twoStep_mem_coset {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀))
    {z : W} (hez : BruhatStep cs ((g : W) * a₀) z)
    (hzf : BruhatStep cs z ((k : W) * a₀)) :
    z * a₀⁻¹ ∈ planeSubgroup M cs P := by
  by_cases hz : (h : W) * a₀ = z
  · rw [← hz, mul_inv_cancel_right]
    exact h.property
  have hplane := graphRoot_square_plane he hez hf hzf hz
  have hroot : (graphRoot hez).val ∈ P := by
    apply (hplane.symm.trans (B.graphRoot_path_plane he hf)).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have href : z * ((g : W) * a₀)⁻¹ ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents hez)).mpr hroot
  convert (planeSubgroup M cs P).mul_mem href g.property using 1 <;> first | (with_reducible_and_instances rfl) | (group)

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {G : Type*} [Group G] {N : CoxeterMatrix Bool}

/-- Exactly two intermediate vertices characterize relative rank two as soon
as one two-edge path exists. Used to rule out skipped ranks after transport. -/
theorem rank_two_of_two_step_bound (ds : CoxeterSystem N G) {x y a b : G}
    (ha : BruhatStep ds x a) (hay : BruhatStep ds a y)
    (hbound : ∀ z, BruhatStep ds x z → BruhatStep ds z y → z = a ∨ z = b) :
    ds.length y = ds.length x + 2 := by
  have hxa := (step_iff_odd ds x a).mp ha
  have hay' := (step_iff_odd ds a y).mp hay
  rw [Nat.odd_iff] at hxa hay'
  have heven : (ds.length y - ds.length x) % 2 = 0 := by omega
  by_contra hlen
  have hlarge : ds.length x + 3 < ds.length y := by omega
  obtain ⟨p,q,hpq,hlevel⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+1) (w := y) (by omega)
  have hp := (hlevel p).mpr (Or.inl rfl)
  have hq := (hlevel q).mpr (Or.inr rfl)
  obtain ⟨r,s,hrs,hlevel'⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+3) hlarge
  have hr := (hlevel' r).mpr (Or.inl rfl)
  have paths : ∀ z, ds.length z = ds.length x+1 ∨ ds.length z = ds.length x+3 →
      BruhatStep ds x z ∧ BruhatStep ds z y := by
    intro z hz
    rw [step_iff_odd,step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    rcases hz with hz | hz <;> omega
  have pp := paths p (Or.inl hp)
  have pq := paths q (Or.inl hq)
  have pr := paths r (Or.inr hr)
  have hpr : p ≠ r := by intro he; rw [he] at hp; omega
  have hqr : q ≠ r := by intro he; rw [he] at hq; omega
  rcases hbound p pp.1 pp.2 with hp' | hp' <;>
    rcases hbound q pq.1 pq.2 with hq' | hq' <;>
    rcases hbound r pr.1 pr.2 with hr' | hr' <;> grind

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem graphRoot_mem_of_coset {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : y*a₀⁻¹ ∈ planeSubgroup M cs P) : (graphRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mp
  convert (planeSubgroup M cs P).mul_mem hy ((planeSubgroup M cs P).inv_mem hx) using 1
  all_goals try with_reducible_and_instances rfl
  group

theorem mem_coset_of_graphRoot {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : (graphRoot h).val ∈ P) : y*a₀⁻¹ ∈ planeSubgroup M cs P := by
  have hm := (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mpr hy
  convert (planeSubgroup M cs P).mul_mem hm hx using 1
  all_goals try with_reducible_and_instances rfl
  group

variable {D : Type*} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

/-- The image of a full relative dihedral interval lies in one maximal plane
coset. This is derived just from the directed graph and distinct vertices. -/
theorem dihedral_image_in_plane
    (f : Interval ds l r → W) (hinj : Function.Injective f)
    (hgraph : ∀ a b : Interval ds l r,
      BruhatStep ds a.val b.val → BruhatStep cs (f a) (f b))
    (hlr : BruhatLE ds l r) (hrank : ds.length l + 2 ≤ ds.length r) :
    ∃ a b : PositiveRoot M cs, a ≠ b ∧
      ∀ z : Interval ds l r,
        f z * (f ⟨l,bruhat_refl ds l,hlr⟩)⁻¹ ∈ planeSubgroup M cs (rootPlane a b) := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  obtain ⟨a,b,hab,ha,hb⟩ := Dihedral.two_interval_elements_length ds lo hi
    (n := ds.length l+1) (by dsimp [lo]; omega) (by dsimp [hi]; omega)
  have cover : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      BruhatStep cs (f p) (f q) := by
    intro p q hlen
    apply hgraph
    rw [Dihedral.step_iff_odd,Nat.odd_iff]
    omega
  have hla := cover lo a ha
  have hlb := cover lo b hb
  have hrootne := graphRoot_ne_of_same_source hla hlb (fun h => hab (hinj h))
  let P := rootPlane (graphRoot hla) (graphRoot hlb)
  refine ⟨graphRoot hla,graphRoot hlb,hrootne,?_⟩
  change ∀ z : Interval ds l r, f z * (f lo)⁻¹ ∈ planeSubgroup M cs P
  have hlo : f lo * (f lo)⁻¹ ∈ planeSubgroup M cs P := by simp
  have hat : f a * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hla hlo (Submodule.subset_span (Set.mem_insert _ _))
  have hbt : f b * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hlb hlo
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  intro z
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val = n →
      f z * (f lo)⁻¹ ∈ planeSubgroup M cs P from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    have hzmin := length_le_of_bruhat ds z.property.1
    by_cases hzlo : z = lo
    · simpa only [hzlo] using hlo
    have hzgt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => hzlo (Subtype.ext h.symm))
    by_cases hzone : ds.length z.val = ds.length l+1
    · obtain ⟨p,q,hpq,hlev⟩ := Dihedral.two_elements_length ds
        (by omega : 0 < ds.length l+1) (w := r) (by omega)
      have ap := (hlev a.val).mp ha
      have bp := (hlev b.val).mp hb
      have zp := (hlev z.val).mp hzone
      have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      have hza : z = a ∨ z = b := by
        apply (show z.val = a.val ∨ z.val = b.val → z = a ∨ z = b from
          fun h => h.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h)))
        grind
      rcases hza with rfl | rfl <;> assumption
    have htwo : ds.length l+2 ≤ ds.length z.val := by omega
    have hexp : ∃ p : Interval ds l r, ds.length p.val+2=ds.length z.val := by
      by_cases he : ds.length z.val = ds.length l+2
      · exact ⟨lo,he.symm⟩
      · obtain ⟨p,q,_,hp,_⟩ := Dihedral.two_interval_elements_length ds lo z
          (n := ds.length z.val-2) (by dsimp [lo]; omega) (by omega)
        exact ⟨p,by omega⟩
    obtain ⟨p,hp⟩ := hexp
    obtain ⟨q,s,hqs,hq,hs⟩ := Dihedral.two_interval_elements_length ds lo z
      (n := ds.length z.val-1) (by dsimp [lo]; omega) (by omega)
    have hp' := ih (ds.length p.val) (by omega) p rfl
    have hq' := ih (ds.length q.val) (by omega) q rfl
    have hs' := ih (ds.length s.val) (by omega) s rfl
    have hpq := cover p q (by omega)
    have hps := cover p s (by omega)
    have hqz := cover q z (by omega)
    have hsz := cover s z (by omega)
    have hplane : rootPlane (graphRoot hpq) (graphRoot hps) = P :=
      rootPlane_eq_of_mem _ _ _ _ hrootne (graphRoot_mem_of_coset hpq hp' hq')
        (graphRoot_mem_of_coset hps hp' hs')
        (graphRoot_ne_of_same_source hpq hps (fun h => hqs (hinj h)))
    have hsquare := graphRoot_square_plane hpq hps hqz hsz (fun h => hqs (hinj h))
    apply mem_coset_of_graphRoot hqz hq'
    apply (hsquare.trans hplane).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
universe u₁ u₂
variable {D : Type u₁} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

theorem exists_interval_length (hlr : BruhatLE ds l r) {n : ℕ}
    (hnl : ds.length l ≤ n) (hnr : n ≤ ds.length r) :
    ∃ z : Interval ds l r, ds.length z.val = n := by
  by_cases hl : n = ds.length l
  · exact ⟨⟨l,bruhat_refl ds l,hlr⟩,hl.symm⟩
  by_cases hr : n = ds.length r
  · exact ⟨⟨r,hlr,bruhat_refl ds r⟩,hr.symm⟩
  obtain ⟨a,b,_,ha,_⟩ := two_interval_elements_length ds
    (⟨l,bruhat_refl ds l,hlr⟩ : Interval ds l r)
    (⟨r,hlr,bruhat_refl ds r⟩ : Interval ds l r)
    (n := n) (by dsimp; omega) (by dsimp; omega)
  exact ⟨a,ha⟩

variable {D' : Type u₂} [Group D'] {N' : CoxeterMatrix Bool}
  (ds' : CoxeterSystem N' D')

theorem map_cover_length
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    {x y : Interval ds l r} (hxy : ds.length y.val = ds.length x.val+1) :
    ds'.length (f y) = ds'.length (f x)+1 := by
  have hstep : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      ds'.length (f p) < ds'.length (f q) := by
    intro p q hpq
    apply (hgraph p q ?_).1
    rw [step_iff_odd,Nat.odd_iff]
    omega
  have hxy' := hstep x y hxy
  have hyr := length_le_of_bruhat ds y.property.2
  by_cases hy : ds.length y.val < ds.length r
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length y.val+1)
      (by have := length_le_of_bruhat ds y.property.1; omega) (by omega)
    have hyz := hstep y z hz
    have hxz := htwo x z (by omega)
    omega
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length x.val-1) (by omega) (by omega)
    have hzx := hstep z x (by omega)
    have hzy := htwo z y (by omega)
    omega

/-- A directed dihedral-interval graph injection which does not stretch any
rank-two interval preserves all relative ranks. -/
theorem map_length_affine
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    (z : Interval ds l r) :
    ds'.length (f z) + ds.length l =
      ds'.length (f ⟨l,bruhat_refl ds l,hlr⟩) + ds.length z.val := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  change ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val=n →
      ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    by_cases he : z=lo
    · simp [he,lo]
    have hlt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => he (Subtype.ext h.symm))
    obtain ⟨p,hp⟩ := exists_interval_length ds hlr (n := ds.length z.val-1)
      (by omega) (by have := length_le_of_bruhat ds z.property.2; omega)
    have ihp := ih (ds.length p.val) (by omega) p rfl
    have hc := map_cover_length ds ds' f hgraph htwo hlr hrank (x := p) (y := z)
      (by omega)
    omega

/-- Once relative covers are recovered, the image exhausts rather than merely
embeds in the target dihedral interval. -/
theorem range_eq_interval_of_rank_two
    (f : Interval ds l r → D') (hinj : Function.Injective f)
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r) :
    Set.range f = {z | BruhatLE ds' (f ⟨l,bruhat_refl ds l,hlr⟩) z ∧
      BruhatLE ds' z (f ⟨r,hlr,bruhat_refl ds r⟩)} := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  have hlen (z : Interval ds l r) : ds'.length (f z)+ds.length l =
      ds'.length (f lo)+ds.length z.val :=
    map_length_affine ds ds' f hgraph htwo hlr hrank z
  have hhi : ds'.length (f hi)+ds.length l=ds'.length (f lo)+ds.length r := hlen hi
  have horder (x y : Interval ds l r) :
      BruhatLE ds' (f x) (f y) ↔ x ≤ y := by
    change BruhatLE ds' (f x) (f y) ↔ BruhatLE ds x.val y.val
    rw [bruhat_iff_length_lt_or_eq,bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg f (Subtype.ext h))
  apply Set.ext
  intro z
  change (∃ x, f x=z) ↔ BruhatLE ds' (f lo) z ∧ BruhatLE ds' z (f hi)
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(horder lo x).mpr x.property.1,(horder x hi).mpr x.property.2⟩
  · intro hz
    by_cases hlo : z=f lo
    · exact ⟨lo,hlo.symm⟩
    by_cases htop : z=f hi
    · exact ⟨hi,htop.symm⟩
    have hzlo := length_lt_of_bruhat_ne ds' hz.1 (Ne.symm hlo)
    have hzhi := length_lt_of_bruhat_ne ds' hz.2 htop
    have hnlo : ds.length l < ds.length l+(ds'.length z-ds'.length (f lo)) := by omega
    have hnhi : ds.length l+(ds'.length z-ds'.length (f lo)) < ds.length r := by omega
    obtain ⟨a,b,hab,ha,hb⟩ := two_interval_elements_length ds lo hi hnlo hnhi
    have hfa : ds'.length (f a)=ds'.length z := by have := hlen a; omega
    have hfb : ds'.length (f b)=ds'.length z := by have := hlen b; omega
    obtain ⟨p,q,hpq,helements⟩ := two_elements_length ds' (by omega : 0<ds'.length z) hzhi
    have hp := (helements (f a)).mp hfa
    have hq := (helements (f b)).mp hfb
    have hr := (helements z).mp rfl
    have hab' : f a ≠ f b := fun h => hab (hinj h)
    have he : z=f a ∨ z=f b := by grind
    rcases he with he | he
    · exact ⟨a,he.symm⟩
    · exact ⟨b,he.symm⟩

end KLInvariance.Dihedral

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
  {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
  {cs : CoxeterSystem M W} {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}

/-- An interval graph isomorphism preserves the exact two-edge intermediate
set, including ambient intermediates not specified as interval data. -/
theorem intervalIso_twoStep_iff
    (e : Interval cs u b ≃o Interval cs' u' b') (x y a c : Interval cs u b)
    (hpaths : ∀ z : W, (BruhatStep cs x.val z ∧ BruhatStep cs z y.val) ↔
      z=a.val ∨ z=c.val) (z : W') :
    (BruhatStep cs' (e x).val z ∧ BruhatStep cs' z (e y).val) ↔
      z=(e a).val ∨ z=(e c).val := by
  constructor
  · intro hz
    let z' : Interval cs' u' b' := ⟨z,
      bruhat_trans cs' (e x).property.1 (Relation.ReflTransGen.single hz.1),
      bruhat_trans cs' (Relation.ReflTransGen.single hz.2) (e y).property.2⟩
    have hz₁ : BruhatStep cs x.val (e.symm z').val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e x (e.symm z')).mp
      simpa only [e.apply_symm_apply] using hz.1
    have hz₂ : BruhatStep cs (e.symm z').val y.val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e (e.symm z') y).mp
      simpa only [e.apply_symm_apply] using hz.2
    rcases (hpaths (e.symm z').val).mp ⟨hz₁,hz₂⟩ with ha | hc
    · have he : e.symm z'=a := Subtype.ext ha
      have he' : z'=e a := by rw [← he,e.apply_symm_apply]
      exact Or.inl (congrArg Subtype.val he')
    · have he : e.symm z'=c := Subtype.ext hc
      have he' : z'=e c := by rw [← he,e.apply_symm_apply]
      exact Or.inr (congrArg Subtype.val he')
  · rintro (rfl | rfl)
    · have h := (hpaths a.val).mpr (Or.inl rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x a).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e a y).mpr h.2⟩
    · have h := (hpaths c.val).mpr (Or.inr rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x c).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e c y).mpr h.2⟩

end KLInvariance

namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

theorem twoStep_interval_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (x y : Interval B.system g k)
    (hlen : B.system.length y.val=B.system.length x.val+2) :
    ∃ a b : Interval B.system g k, a ≠ b ∧ ∀ z : W,
      (BruhatStep cs ((x.val : W)*a₀) z ∧ BruhatStep cs z ((y.val : W)*a₀)) ↔
        z=(a.val : W)*a₀ ∨ z=(b.val : W)*a₀ := by
  obtain ⟨a,b,hab,hpaths⟩ := Dihedral.two_step_rank_two B.system hlen
  have ha := (hpaths a).mpr (Or.inl rfl)
  have hb := (hpaths b).mpr (Or.inr rfl)
  let ai : Interval B.system g k := ⟨a,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single ha.1),
    bruhat_trans B.system (Relation.ReflTransGen.single ha.2) y.property.2⟩
  let bi : Interval B.system g k := ⟨b,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single hb.1),
    bruhat_trans B.system (Relation.ReflTransGen.single hb.2) y.property.2⟩
  have he := (B.coset_step_iff hmin x.val a).mpr ha.1
  have hf := (B.coset_step_iff hmin a y.val).mpr ha.2
  refine ⟨ai,bi,fun h => hab (congrArg Subtype.val h),fun z => ?_⟩
  constructor
  · intro hz
    let z' : planeSubgroup M cs P := ⟨z*a₀⁻¹,B.twoStep_mem_coset he hf hz.1 hz.2⟩
    have hz' : (z' : W)*a₀=z := by dsimp [z']; group
    have hp : BruhatStep B.system x.val z' ∧ BruhatStep B.system z' y.val := by
      constructor
      · exact (B.coset_step_iff hmin x.val z').mp (hz' ▸ hz.1)
      · exact (B.coset_step_iff hmin z' y.val).mp (hz' ▸ hz.2)
    rcases (hpaths z').mp hp with hza | hzb
    · exact Or.inl (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hza))
    · exact Or.inr (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hzb))
  · rintro (rfl | rfl)
    · exact ⟨he,hf⟩
    · exact ⟨(B.coset_step_iff hmin x.val b).mpr hb.1,
        (B.coset_step_iff hmin b y.val).mpr hb.2⟩

end
end KLInvariance.TitsSpace.PlaneBasis

namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section


theorem transport_interval {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (hgk : BruhatLE B.system g k)
    (hrank : B.system.length g+2 ≤ B.system.length k)
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b') :
    ∃ (P' : Submodule ℝ (I' → ℝ)) (B' : PlaneBasis (M := M') (cs := cs') P')
      (a' : W') (F : Interval B.system g k → planeSubgroup M' cs' P'),
      (∀ z ∈ planeSubgroup M' cs' P', cs'.length a' ≤ cs'.length (z*a')) ∧
      Function.Injective F ∧
      (∀ z, (F z : W')*a' = (e (B.cosetIntervalMap hmin hlo hhi z)).val) ∧
      (∀ x y, BruhatLE B'.system (F x) (F y) ↔ x ≤ y) ∧
      (∀ x y, BruhatStep B'.system (F x) (F y) ↔ BruhatStep B.system x.val y.val) ∧
      (∀ z, B'.system.length (F z)+B.system.length g =
        B'.system.length (F ⟨g,bruhat_refl B.system g,hgk⟩)+B.system.length z.val) ∧
      Set.range F = {z | BruhatLE B'.system (F ⟨g,bruhat_refl B.system g,hgk⟩) z ∧
        BruhatLE B'.system z (F ⟨k,hgk,bruhat_refl B.system k⟩)} := by
  let inc := B.cosetIntervalMap hmin hlo hhi
  let f : Interval B.system g k → W' := fun z => (e (inc z)).val
  let lo : Interval B.system g k := ⟨g,bruhat_refl B.system g,hgk⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact inc.injective (e.injective (Subtype.ext h))
  have hgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep cs' (f x) (f y) := by
    exact (intervalIso_bruhatStep_iff_general cs cs' e (inc x) (inc y)).mpr
      ((B.coset_step_iff hmin x.val y.val).mpr h)
  obtain ⟨α,β,hαβ,hplane⟩ := dihedral_image_in_plane B.system f hinj hgraph hgk hrank
  let P' := rootPlane α β
  obtain ⟨B'⟩ := nonempty_planeBasis α β hαβ
  obtain ⟨a',g₀,hg₀,hg₀a,hmin'⟩ := planeCoset_exists_minimal M' cs' P' (f lo)
  have hmem (z : Interval B.system g k) : f z*a'⁻¹ ∈ planeSubgroup M' cs' P' := by
    convert (planeSubgroup M' cs' P').mul_mem (hplane z) hg₀ using 1
    all_goals try with_reducible_and_instances rfl
    change f z*a'⁻¹=f z*(f lo)⁻¹*g₀
    rw [hg₀a]
    group
  let F : Interval B.system g k → planeSubgroup M' cs' P' := fun z => ⟨f z*a'⁻¹,hmem z⟩
  have hF (z : Interval B.system g k) : (F z : W')*a'=f z := by
    dsimp [F]; group
  have hFinj : Function.Injective F := by
    intro x y h
    apply hinj
    rw [← hF x,← hF y,h]
  have hFgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep B'.system (F x) (F y) := by
    apply (B'.coset_step_iff hmin' (F x) (F y)).mp
    rw [hF x,hF y]
    exact hgraph x y h
  have htwo (x y : Interval B.system g k)
      (hlen : B.system.length y.val=B.system.length x.val+2) :
      B'.system.length (F y)=B'.system.length (F x)+2 := by
    obtain ⟨a,c,hac,hpaths⟩ := B.twoStep_interval_iff hmin x y hlen
    have hpaths' (z : W') : (BruhatStep cs' (f x) z ∧ BruhatStep cs' z (f y)) ↔
        z=f a ∨ z=f c := intervalIso_twoStep_iff e (inc x) (inc y) (inc a) (inc c) hpaths z
    have hpa := (hpaths' (f a)).mpr (Or.inl rfl)
    have hxa : BruhatStep B'.system (F x) (F a) := by
      apply (B'.coset_step_iff hmin' (F x) (F a)).mp
      simpa only [hF] using hpa.1
    have hay : BruhatStep B'.system (F a) (F y) := by
      apply (B'.coset_step_iff hmin' (F a) (F y)).mp
      simpa only [hF] using hpa.2
    apply Dihedral.rank_two_of_two_step_bound B'.system hxa hay (b := F c)
    intro z hxz hzy
    have hp₁ := (B'.coset_step_iff hmin' (F x) z).mpr hxz
    have hp₂ := (B'.coset_step_iff hmin' z (F y)).mpr hzy
    rw [hF x] at hp₁
    rw [hF y] at hp₂
    rcases (hpaths' ((z : W')*a')).mp ⟨hp₁,hp₂⟩ with he | he
    · exact Or.inl (Subtype.ext (mul_right_cancel (he.trans (hF a).symm)))
    · exact Or.inr (Subtype.ext (mul_right_cancel (he.trans (hF c).symm)))
  have hlen := Dihedral.map_length_affine B.system B'.system F hFgraph htwo hgk hrank
  have horder (x y : Interval B.system g k) : BruhatLE B'.system (F x) (F y) ↔ x ≤ y := by
    change BruhatLE B'.system (F x) (F y) ↔ BruhatLE B.system x.val y.val
    rw [Dihedral.bruhat_iff_length_lt_or_eq,Dihedral.bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hFinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg F (Subtype.ext h))
  refine ⟨P',B',a',F,hmin',hFinj,hF,horder,?_,hlen,?_⟩
  · intro x y
    rw [Dihedral.step_iff_odd,Dihedral.step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    have hx := hlen x
    have hy := hlen y
    omega
  · exact Dihedral.range_eq_interval_of_rank_two B.system B'.system F hFinj
      hFgraph htwo hgk hrank

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem inverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : rootInverted w a) (hb : rootInverted w b) :
    rootInverted w c := by
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha i))
    (mul_nonpos_of_nonneg_of_nonpos hs (hb i))

/-- Incoming graph labels are actual inversions at their upper vertex. -/
theorem graphRoot_inverted_target {x y : W} (h : BruhatStep cs x y) :
    rootInverted y (graphRoot h) := by
  apply ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 y).mpr
  refine ⟨h.label_reflection, ?_⟩
  have he : (y*x⁻¹)*y=x := by
    calc
      (y*x⁻¹)*y = (y*x⁻¹)*((y*x⁻¹)*x) := by group
      _ = x := by rw [← mul_assoc,h.label_reflection.mul_self,one_mul]
  simpa only [he] using h.1

/-- Outgoing graph labels are actual noninversions at their lower vertex. -/
theorem graphRoot_not_inverted_source {x y : W} (h : BruhatStep cs x y) :
    ¬ rootInverted x (graphRoot h) := by
  intro hi
  have hh := ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 x).mp hi
  have he : (y*x⁻¹)*x=y := by group
  have hh' := hh.2
  rw [he] at hh'
  exact lt_asymm h.1 hh'

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- In a plane with its first simple root inverted, every noninverted root
is later than every inverted root. This uses convexity, not a signed-index
formula for a particular realization. -/
theorem slope_lt_of_inverted_left (w : W) (hl : rootInverted w B.left)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b := by
  by_contra h
  have hba : geometricSlope b < geometricSlope a :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hlb : geometricSlope B.left < geometricSlope b :=
    lt_of_le_of_ne (B.left_min b hbP) (fun he => hb (geometricSlope_injective he ▸ hl))
  have heq : rootPlane B.left a = P :=
    rootPlane_eq_of_mem B.left B.right B.left a B.distinct
      (Submodule.subset_span (Set.mem_insert _ _))
      (B.plane_eq.ge haP) (fun he => by rw [he] at hlb; exact (lt_asymm hlb hba)) |>.trans B.plane_eq
  obtain ⟨r,s,hr,hs,hc⟩ := positive_combination_of_slope_between B.left a b
    (heq.symm ▸ hbP) hlb hba
  exact hb (inverted_of_positive_combination w B.left a b hr.le hs.le hc hl ha)

/-- The other angular cut, when the last simple root is inverted. -/
theorem slope_lt_of_inverted_right (w : W) (hr : rootInverted w B.right)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope b < geometricSlope a := by
  by_contra h
  have hab : geometricSlope a < geometricSlope b :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hbr : geometricSlope b < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max b hbP) (fun he => hb (geometricSlope_injective he ▸ hr))
  have har : a ≠ B.right := by
    intro he
    rw [he] at hab
    exact lt_asymm hbr hab
  have heq : rootPlane a B.right = P :=
    (rootPlane_eq_of_mem B.left B.right a B.right B.distinct
      (B.plane_eq.ge haP) (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      har).trans B.plane_eq
  obtain ⟨r,s,hrr,hss,hc⟩ := positive_combination_of_slope_between a B.right b
    (heq.symm ▸ hbP) hab hbr
  exact hb (inverted_of_positive_combination w a B.right b hrr.le hss.le hc ha hr)

/-- In the mixed-sign case the angular cut is determined by the first
canonical simple root. In particular the comparison of consecutive path
labels depends only on their middle vertex. -/
theorem slope_lt_iff_inverted_left (w : W)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b ↔ rootInverted w B.left := by
  constructor
  · intro hab
    by_contra hl
    have hr : rootInverted w B.right := by
      by_contra hr
      obtain ⟨r,s,hrr,hss,he⟩ := B.positive_cone a haP
      exact noninverted_of_positive_combination w B.left B.right a hrr hss he hl hr ha
    exact lt_asymm hab (B.slope_lt_of_inverted_right w hr a b haP hbP ha hb)
  · intro hl
    exact B.slope_lt_of_inverted_left w hl a b haP hbP ha hb

/-- The exact middle-vertex test for two ascending graph arrows with both
labels in this root plane. -/
theorem consecutive_slopes_iff {x y z : W}
    (hxy : BruhatStep cs x y) (hyz : BruhatStep cs y z)
    (ha : (graphRoot hxy).val ∈ P) (hb : (graphRoot hyz).val ∈ P) :
    geometricSlope (graphRoot hxy) < geometricSlope (graphRoot hyz) ↔
      rootInverted y B.left :=
  B.slope_lt_iff_inverted_left y _ _ ha hb
    (graphRoot_inverted_target hxy) (graphRoot_not_inverted_source hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- A nonzero length below an existing greater length has exactly one left
simple descent. This is not asserted for a finite dihedral longest element. -/
theorem unique_leftDescent (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    ∃! i : Bool, cs.IsLeftDescent w i := by
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one (w := w) (by
    intro he
    rw [he,cs.length_one] at hw
    omega)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hj' : j = !i := by cases i <;> cases j <;> simp_all
  have he : cs.wordProd (alt i (cs.length w)) =
      cs.wordProd (alt (!i) (cs.length w)) := by
    rw [← eq_alt_of_descent cs i hi, ← hj', ← eq_alt_of_descent cs j hj]
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs hw hz
  have all_eq (v : W) (hv : cs.length v = cs.length w) : v=w := by
    obtain ⟨k,hk⟩ := exists_alt cs v
    rw [hv] at hk
    have hki : k=i ∨ k=(!i) := by cases k <;> cases i <;> simp
    rcases hki with hki | hki
    · rw [hki] at hk
      exact hk.trans (eq_alt_of_descent cs i hi).symm
    · rw [hki] at hk
      exact hk.trans (he.symm.trans (eq_alt_of_descent cs i hi).symm)
  exact hab ((all_eq a ((hab' a).mpr (.inl rfl))).trans
    (all_eq b ((hab' b).mpr (.inr rfl))).symm)

end
end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The ambient sign of a canonical plane root in a minimal coset is the
intrinsic simple-descent sign, with the original left labels. -/
theorem simpleRoot_inverted_coset_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) (i : Bool) :
    rootInverted ((w : W)*a₀) (B.simpleRoot i) ↔ B.system.IsLeftDescent w i := by
  change (∀ k, action M cs ((w : W)*a₀)⁻¹ (B.simpleRoot i).val k ≤ 0) ↔ _
  rw [root_inversion_coset_iff hmin w.property (B.simpleRoot i).property.1
    (B.simpleRoot_mem i)]
  have hr : Represents M cs (B.system.simple i : W) (B.simpleRoot i).val := by
    rw [B.system_simple]
    exact rootReflection_represents M cs _
  rw [B.inversion_iff hr (B.simpleRoot_mem i) (B.simpleRoot i).property.2 w]
  exact B.system.isLeftInversion_simple_iff_isLeftDescent w i

theorem edgeRoot_plane {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    (B.edgeRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents
    ((B.bruhatStep_iff x y).mpr h))).mp
  exact (planeSubgroup M cs P).mul_mem y.property
    ((planeSubgroup M cs P).inv_mem x.property)

/-- In the intrinsic system, the middle-vertex test uses its actual left
simple generator; it therefore applies to any induced dihedral realization. -/
theorem edgeRoot_slopes_iff {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      B.system.IsLeftDescent y false := by
  unfold edgeRoot
  rw [B.consecutive_slopes_iff ((B.bruhatStep_iff x y).mpr hxy)
    ((B.bruhatStep_iff y z).mpr hyz) (B.edgeRoot_plane hxy) (B.edgeRoot_plane hyz)]
  have hmin : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  simpa only [mul_one, simpleRoot, Bool.false_eq_true, ↓reduceIte] using
    B.simpleRoot_inverted_coset_iff hmin y false

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable
theorem edgeRoot_ne_of_path {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    B.edgeRoot hxy ≠ B.edgeRoot hyz :=
  graphRoot_ne_of_path ((B.bruhatStep_iff x y).mpr hxy) ((B.bruhatStep_iff y z).mpr hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Genuine Dyer identification for geometric orders adapted to a fixed top.
The path values below are defined from actual reflection edges; equality with
`Hecke.rTilde` will be proved by its genuine simple-descent recurrence. -/
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

theorem rootLabel_ne_of_join (e f : Edge cs) (h : target cs e = source cs f) :
    rootLabel cs e ≠ rootLabel cs f := by
  rcases e with ⟨⟨x,y⟩,he⟩
  rcases f with ⟨⟨z,w⟩,hf⟩
  change y=z at h
  subst z
  exact graphRoot_ne_of_path he hf

end
end KLInvariance.AdaptedDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
theorem sortedSchedule_nodup (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedSchedule_pairwise (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Pairwise (fun e f => score f ≤ score e) :=
  List.pairwise_mergeSort' _ _

end
end KLInvariance.SchedulePaths

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/

section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem simple_rotation (cs : CoxeterSystem M W) :
    cs.simple false * rotation cs = (rotation cs)⁻¹ * cs.simple false := by
  simp only [rotation, mul_inv_rev, cs.inv_simple]
  rw [cs.simple_mul_simple_cancel_left, mul_assoc, cs.simple_mul_simple_self, mul_one]

 theorem simple_rotation_zpow (cs : CoxeterSystem M W) (n : ℤ) :
    cs.simple false * rotation cs ^ n = rotation cs ^ (-n) * cs.simple false := by
  have h : SemiconjBy (cs.simple false) (rotation cs) (rotation cs)⁻¹ :=
    simple_rotation cs
  have hh := h.zpow_right n
  change cs.simple false * rotation cs ^ n = ((rotation cs)⁻¹) ^ n * cs.simple false at hh
  simpa only [inv_zpow, zpow_neg] using hh

 theorem exists_indexWord (cs : CoxeterSystem M W) (w : W) :
    ∃ i : ℤ, |i| = (cs.length w : ℤ) ∧ indexWord cs i = w := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  cases i
  · exact ⟨cs.length w, by simp, (indexWord_nat cs _).trans hi.symm⟩
  · exact ⟨-(cs.length w : ℤ), by simp, (indexWord_neg_nat cs _).trans hi.symm⟩

/-- A reflection acts on the signed index line by reflection in its midpoint.
Finite dihedral groups are handled by equality in the group, without choosing
residue representatives here. -/
 theorem indexWord_reflection_mul (cs : CoxeterSystem M W) {a : ℤ} (ha : Odd a)
    (i : ℤ) : indexWord cs a * indexWord cs i = indexWord cs (a-i) := by
  obtain ⟨k,hk⟩ := ha
  have hk' : a = 2*k+1 := by omega
  rw [hk',indexWord_odd]
  rcases Int.even_or_odd i with ⟨l,hl⟩ | ⟨l,hl⟩
  · have hl' : i=2*l := by omega
    rw [hl',indexWord_even,show 2*k+1-2*l=2*(k-l)+1 by ring,indexWord_odd]
    rw [mul_assoc, simple_rotation_zpow, ← mul_assoc, ← zpow_add]
    congr 2
  · have hl' : i=2*l+1 := by omega
    rw [hl',indexWord_odd,show 2*k+1-(2*l+1)=2*(k-l) by ring,indexWord_even]
    calc
      (rotation cs ^ k * cs.simple false) * (rotation cs ^ l * cs.simple false) =
          rotation cs ^ k * (cs.simple false * rotation cs ^ l) * cs.simple false := by group
      _ = rotation cs ^ k * (rotation cs ^ (-l) * cs.simple false) * cs.simple false := by
        rw [simple_rotation_zpow]
      _ = rotation cs ^ (k-l) := by
        rw [← mul_assoc, mul_assoc (rotation cs ^ k * rotation cs ^ (-l)),
          cs.simple_mul_simple_self, mul_one, ← zpow_add]
        congr 1

 theorem indexWord_label (cs : CoxeterSystem M W) {i j : ℤ} (h : Odd (i+j)) :
    indexWord cs j * (indexWord cs i)⁻¹ = indexWord cs (i+j) := by
  have he := indexWord_reflection_mul cs h i
  rw [show i+j-i=j by omega] at he
  rw [← he]
  group

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem length_indexWord (cs : CoxeterSystem M W) {i : ℤ} {w : W}
    (h : i.natAbs ≤ cs.length w) : cs.length (indexWord cs i) = i.natAbs := by
  obtain hi|hi := le_total 0 i
  · have he : i=(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonneg hi]
    nth_rw 1 [he]
    exact length_indexWord_nat cs h
  · have he : i= -(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonpos hi,neg_neg]
    nth_rw 1 [he]
    exact length_indexWord_neg_nat cs h

 theorem leftDescent_alt (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (hn : 0<n) (h : n ≤ cs.length w) :
    cs.IsLeftDescent (cs.wordProd (alt i n)) i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  unfold CoxeterSystem.IsLeftDescent
  rw [length_alt_le_length cs i h,alt_succ,cs.wordProd_cons,cs.simple_mul_simple_cancel_left]
  have hh := cs.length_wordProd_le (alt (!i) k)
  rw [length_alt] at hh
  omega

 theorem indexWord_add_even (cs : CoxeterSystem M W) (i n : ℤ) :
    indexWord cs (i+2*n) = rotation cs ^ n * indexWord cs i := by
  have hm : (i+2*n)%2=i%2 := by omega
  have hd : (i+2*n)/2=i/2+n := by omega
  simp only [indexWord,hm,hd,zpow_add]
  split_ifs
  · exact (Commute.zpow_zpow_self (rotation cs) (i/2) n).eq
  · rw [← mul_assoc,(Commute.zpow_zpow_self (rotation cs) (i/2) n).eq,mul_assoc]

/-- The maximal-length case supplies the precise signed period, without an
extra finiteness hypothesis or a numerical cosine restriction. -/
 theorem rotation_pow_max (cs : CoxeterSystem M W) (w : W)
    (hmax : ∀ z, cs.length z ≤ cs.length w) : rotation cs ^ cs.length w = 1 := by
  have hd (i : Bool) : cs.IsLeftDescent w i := by
    have hle := hmax (cs.simple i*w)
    have hne := cs.length_simple_mul w i
    unfold CoxeterSystem.IsLeftDescent
    omega
  have he : indexWord cs (cs.length w) = indexWord cs (-(cs.length w:ℤ)) := by
    rw [indexWord_nat,indexWord_neg_nat,← eq_alt_of_descent cs false (hd false),
      ← eq_alt_of_descent cs true (hd true)]
  have hp := indexWord_add_even cs (-(cs.length w:ℤ)) (cs.length w)
  rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)=(cs.length w:ℤ) by ring,
    zpow_natCast,he] at hp
  exact mul_right_cancel (show rotation cs ^ cs.length w * indexWord cs (-(cs.length w:ℤ)) =
      1 * indexWord cs (-(cs.length w:ℤ)) by simpa only [one_mul] using hp.symm)

 theorem indexWord_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i k : ℤ) :
    indexWord cs (i+2*(N:ℤ)*k) = indexWord cs i := by
  rw [show i+2*(N:ℤ)*k=i+2*((N:ℤ)*k) by ring,indexWord_add_even,zpow_mul,zpow_natCast,hN,
    one_zpow,one_mul]

 theorem indexWord_mod_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i : ℤ) :
    indexWord cs (i%(2*(N:ℤ))) = indexWord cs i := by
  have hp := indexWord_period cs hN (i%(2*(N:ℤ))) (i/(2*(N:ℤ)))
  rw [Int.emod_add_mul_ediv] at hp
  exact hp.symm

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem prefixRoot_strictMono (w : planeSubgroup M cs P) :
    StrictMonoOn (fun n => geometricSlope (B.prefixRoot w n)) (Set.Iio (B.system.length w)) := by
  apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.prefixRoot w n) < geometricSlope (B.prefixRoot w (n+1))
  rw [prefixRoot,prefixRoot,dite_eq_left hn,dite_eq_left hn']
  apply (B.edgeRoot_slopes_iff _ _).mpr
  rw [indexWord_nat]
  exact leftDescent_alt B.system false (by omega) hn'.le

 theorem negPrefixRoot_strictAnti (w : planeSubgroup M cs P) :
    StrictAntiOn (fun n => geometricSlope (B.negPrefixRoot w n))
      (Set.Iio (B.system.length w)) := by
  apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.negPrefixRoot w (n+1)) < geometricSlope (B.negPrefixRoot w n)
  rw [negPrefixRoot,negPrefixRoot,dite_eq_left hn,dite_eq_left hn']
  have ht : B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) true := by
    rw [indexWord_neg_nat]
    exact leftDescent_alt B.system true (by omega) hn'.le
  have hlen := length_indexWord_neg_nat B.system hn'.le
  have hu := unique_leftDescent B.system (w := indexWord B.system (-((n+1:ℕ):ℤ)))
    (z := w) (by rw [hlen]; omega) (by rw [hlen]; omega)
  have hf : ¬B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) false := by
    intro hf
    obtain ⟨i,_,hi⟩ := hu
    have h1 := hi true ht
    have h2 := hi false hf
    simp_all
  have hnlt := (B.edgeRoot_slopes_iff (neg_indexWord_step B.system hn)
    (neg_indexWord_step B.system hn')).not.mpr hf
  apply lt_of_le_of_ne (le_of_not_gt hnlt)
  intro he
  have he' := geometricSlope_injective he
  exact graphRoot_ne_of_path
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn))
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn')) he'.symm

 theorem edgeRoot_eq_of_label {x y z w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzw : BruhatStep B.system z w)
    (he : y*x⁻¹=w*z⁻¹) : B.edgeRoot hxy = B.edgeRoot hzw := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  exact congrArg (fun z : planeSubgroup M cs P => (z : W)) he

 theorem prefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (2*(n:ℤ)+1)) :
    B.prefixRoot w n = B.edgeRoot hxy := by
  rw [prefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

 theorem negPrefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (-(2*(n:ℤ)+1))) :
    B.negPrefixRoot w n = B.edgeRoot hxy := by
  rw [negPrefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.SignedDihedral
noncomputable section

 attribute [local instance] OAI.KLInvariance.SignedDihedral.instDecidable_solutions
theorem before_same_source_pos {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : 0 < j) :
    Before (i+j) (i+z) ↔ z < 0 ∨ j < z := by
  rw [abs_of_pos hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_same_source_neg {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : j < 0) :
    Before (i+j) (i+z) ↔ z < 0 ∧ j < z := by
  rw [abs_of_neg hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_next_source {i j z : ℤ} (hij : |i| < |j|)
    (hjz : |j| < |z|) :
    Before (i+j) (j+z) ↔ 0 < j := by
  obtain hj | hj := le_total 0 j
  · rw [abs_of_nonneg hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonneg hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonneg hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega
  · rw [abs_of_nonpos hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonpos hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonpos hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega

 theorem midpoint_mod {m a : ℤ} (_hm : 0 < m) (ha : -2*m < a) (ha' : a < 2*m) :
    a % (2*m) = if 0 ≤ a then a else 2*m+a := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h ha'
  · have he : a % (2*m) = (a+2*m) % (2*m) := by simp
    rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- For two outgoing edges at the same vertex, reduction modulo the period
has no wrap-around exception in the midpoint comparison table. -/
 theorem finite_before_same {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |i| < |z|)
    (hjM : -m < j ∧ j ≤ m) (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (i+z) % (2*m) ↔ Before (i+j) (i+z) := by
  have hjabs : |j| ≤ m := abs_le.mpr (by omega)
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hiabs := abs_lt.mp (hi.trans_le hjabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem finite_before_next {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |j| < |z|)
    (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (j+z) % (2*m) ↔ Before (i+j) (j+z) := by
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hjabs := abs_lt.mp (hz.trans_le hzabs)
  have hiabs := abs_lt.mp ((hi.trans hz).trans_le hzabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonneg hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonpos hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem eligible_ranks_card (L k : ℕ) :
    ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card = k := by
  classical
  have hc : (Finset.range k).card =
      ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card := by
    apply Finset.card_bij (fun a _ => L+1+2*a)
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at ha ⊢
      omega
    · intro a ha b hb he
      omega
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at hb
      refine ⟨(b-L-1)/2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
  simpa only [Finset.card_range] using hc.symm

 theorem arrowAfter_self (i j : ℤ) : arrowAfter i (i+j) j = 0 := by
  have hb : ¬ Before (i+j) (i+j) := by
    dsimp [Before]
    omega
  simp only [arrowAfter, hb, and_false, ite_false, if_false]

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem length_indexWord_unbounded (cs : CoxeterSystem M W)
    (hu : ∀ n : ℕ, ∃ w, n ≤ cs.length w) (i : ℤ) :
    cs.length (indexWord cs i) = i.natAbs := by
  obtain ⟨w,hw⟩ := hu i.natAbs
  exact length_indexWord cs hw

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem edgeRoot_inverted_iff {x y : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (w : planeSubgroup M cs P) :
    rootInverted (w:W) (B.edgeRoot hxy) ↔ B.system.length ((y*x⁻¹)*w)<B.system.length w := by
  have hh := B.inversion_iff (t := y*x⁻¹)
    (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
    (B.edgeRoot_plane hxy) (B.edgeRoot hxy).property.2 w
  change rootInverted (w:W) (B.edgeRoot hxy) ↔ _ at hh
  rw [hh]
  exact and_iff_right hxy.label_reflection

 theorem edgeRoot_positive_lt_negative
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    (k l : ℕ)
    (hx : y*x⁻¹=indexWord B.system (2*(k:ℤ)+1))
    (hz : t*z⁻¹=indexWord B.system (-(2*(l:ℤ)+1))) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) := by
  let w := indexWord B.system ((k+1:ℕ):ℤ)
  have hi : rootInverted (w:W) (B.edgeRoot hxy) := by
    rw [B.edgeRoot_inverted_iff,hx]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : 2*(k:ℤ)+1-((k+1:ℕ):ℤ)=(k:ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_natCast]
    omega
  have hn : ¬rootInverted (w:W) (B.edgeRoot hzt) := by
    rw [B.edgeRoot_inverted_iff,hz]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : -(2*(l:ℤ)+1)-((k+1:ℕ):ℤ) = -((2*l+k+2:ℕ):ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_neg,Int.natAbs_natCast]
    omega
  have hd : B.system.IsLeftDescent w false := by
    obtain ⟨w',hw'⟩ := hu (k+1)
    change B.system.IsLeftDescent (indexWord B.system ((k+1:ℕ):ℤ)) false
    rw [indexWord_nat]
    exact leftDescent_alt B.system false (by omega) hw'
  have hm : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  have hl : rootInverted (w:W) B.left := by
    have hh := (B.simpleRoot_inverted_coset_iff hm w false).mpr hd
    simpa only [mul_one,simpleRoot,Bool.false_eq_true,↓reduceIte] using hh
  exact B.slope_lt_of_inverted_left (w:W) hl _ _ (B.edgeRoot_plane hxy)
    (B.edgeRoot_plane hzt) hi hn

/-- The two angular rays of an infinite canonical dihedral subsystem, with
actual ambient labels, have precisely the source's signed-midpoint order. -/
 theorem edgeRoot_infinite_order
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      SignedDihedral.Before a b := by
  have repr (q : ℤ) (hq : Odd q) :
      ∃ k : ℕ, q=2*(k:ℤ)+1 ∨ q= -(2*(k:ℤ)+1) := by
    have habs := Int.natCast_natAbs q
    have ho : q.natAbs % 2=1 := by
      rw [Int.odd_iff] at hq
      rcases le_total 0 q with h|h
      · rw [abs_of_nonneg h] at habs
        omega
      · rw [abs_of_nonpos h] at habs
        omega
    refine ⟨q.natAbs/2,?_⟩
    rcases le_total 0 q with h|h
    · left
      rw [abs_of_nonneg h] at habs
      omega
    · right
      rw [abs_of_nonpos h] at habs
      omega
  obtain ⟨k,hk|hk⟩ := repr a ha <;> obtain ⟨l,hl|hl⟩ := repr b hb
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.prefixRoot_eq_edgeRoot hxy hk' hx,← B.prefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.prefixRoot_strictMono w
    have he : geometricSlope (B.prefixRoot w k) < geometricSlope (B.prefixRoot w l) ↔ k<l :=
      hs.lt_iff_lt hk' hl'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hxy hzt k l hx hz
    have hbefore : SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_true hh hbefore
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hzt hxy l k hz hx
    have hn := not_lt_of_gt hh
    have hbefore : ¬SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_false hn hbefore
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.negPrefixRoot_eq_edgeRoot hxy hk' hx,← B.negPrefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.negPrefixRoot_strictAnti w
    have he : geometricSlope (B.negPrefixRoot w k) < geometricSlope (B.negPrefixRoot w l) ↔ l<k := by
      constructor
      · intro h
        by_contra hn
        rcases lt_or_eq_of_le (le_of_not_gt hn) with hkl | rfl
        · exact (not_lt_of_gt (hs hk' hl' hkl)) h
        · exact (lt_irrefl _) h
      · exact hs hl' hk'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem max_length_pos (w : planeSubgroup M cs P)
    (hmax : ∀ z, B.system.length z ≤ B.system.length w) : 0 < B.system.length w := by
  have h := hmax (B.system.simple false)
  rw [B.system.length_simple] at h
  omega

 theorem odd_residue_repr {N : ℕ} (hN : 0<N) {a : ℤ} (ha : Odd a) :
    ∃ k : ℕ, k<N ∧ a % (2*(N:ℤ)) = 2*(k:ℤ)+1 := by
  have hl := Int.emod_nonneg a (by omega : (2*(N:ℤ))≠0)
  have hu := Int.emod_lt_of_pos a (by omega : 0<2*(N:ℤ))
  have hp : (a%(2*(N:ℤ)))%2=1 := by
    rw [Int.emod_emod_of_dvd a (by exact dvd_mul_right 2 (N:ℤ))]
    exact Int.odd_iff.mp ha
  refine ⟨(a%(2*(N:ℤ))).toNat/2, ?_, ?_⟩ <;> omega

/-- The actual ambient angular order in a finite canonical plane subsystem
is the increasing residue order on odd doubled midpoints. -/
 theorem edgeRoot_finite_order
    (w : planeSubgroup M cs P) (hmax : ∀ z, B.system.length z ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      a % (2*(B.system.length w:ℤ)) < b % (2*(B.system.length w:ℤ)) := by
  obtain ⟨k,hk,he⟩ := odd_residue_repr (B.max_length_pos w hmax) ha
  obtain ⟨l,hl,hf⟩ := odd_residue_repr (B.max_length_pos w hmax) hb
  have hp := rotation_pow_max B.system w hmax
  rw [← indexWord_mod_period B.system hp a, he] at hx
  rw [← indexWord_mod_period B.system hp b, hf] at hz
  rw [← B.prefixRoot_eq_edgeRoot hxy hk hx,← B.prefixRoot_eq_edgeRoot hzt hl hz]
  rw [(B.prefixRoot_strictMono w).lt_iff_lt hk hl,he,hf]
  omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 attribute [local instance] OAI.KLInvariance.Dihedral.instDecidableEq_solutions
theorem indexWord_pos_ne_neg (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (hn : 0<n) (hw : n < cs.length w) : indexWord cs n ≠ indexWord cs (-(n:ℤ)) := by
  have hp := leftDescent_alt cs false hn hw.le
  have hm := leftDescent_alt cs true hn hw.le
  rw [← indexWord_nat] at hp
  rw [← indexWord_neg_nat] at hm
  intro he
  rw [← he] at hm
  have hl := length_indexWord_nat cs hw.le
  obtain ⟨i,_,hi⟩ := unique_leftDescent cs (w := indexWord cs n) (z := w)
    (by rw [hl]; exact hn) (by rw [hl]; exact hw)
  have hf := hi false hp
  have ht := hi true hm
  simp_all

 theorem lower_length_fiber (cs : CoxeterSystem M W) (c : W) {n : ℕ}
    (hc : n < cs.length c) :
    (lowerFinset cs c).filter (fun z => cs.length z=n) =
      {indexWord cs n,indexWord cs (-(n:ℤ))} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := exists_alt cs z
    rw [hz.2] at hi
    cases i
    · exact Or.inl (hi.trans (indexWord_nat cs n).symm)
    · exact Or.inr (hi.trans (indexWord_neg_nat cs n).symm)
  · rintro (rfl|rfl)
    · have hl := length_indexWord_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩
    · have hl := length_indexWord_neg_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩

 theorem lower_zero_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=0) = {1} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · exact fun hz => cs.length_eq_zero_iff.mp hz.2
  · rintro rfl
    exact ⟨one_bruhat cs c,cs.length_one⟩

 theorem lower_top_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=cs.length c) = {c} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · intro hz
    by_contra hne
    have hl := length_lt_of_bruhat_ne cs hz.1 hne
    omega
  · rintro rfl
    exact ⟨bruhat_refl cs _,rfl⟩

/-- Actual finite dihedral lower ideals have two internal alternating rays
and a singleton top. The doubled identity contributes zero. -/
 theorem sum_lower_signed (cs : CoxeterSystem M W) (c : W)
    {A : Type*} [AddCommMonoid A] (f : W → A) (h1 : f 1=0) :
    ∑ z ∈ lowerFinset cs c, f z =
      (∑ n ∈ Finset.range (cs.length c),
        (f (indexWord cs n)+f (indexWord cs (-(n:ℤ))))) + f c := by
  classical
  have hmap : ∀ z ∈ lowerFinset cs c, cs.length z ∈ Finset.range (cs.length c+1) := by
    intro z hz
    have hl := length_le_of_bruhat cs ((mem_lowerFinset cs c z).mp hz)
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap f,Finset.sum_range_succ,lower_top_fiber,
    Finset.sum_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hc := Finset.mem_range.mp hn
  by_cases hz : n=0
  · subst n
    rw [lower_zero_fiber]
    simp only [Finset.sum_singleton,indexWord_nat,indexWord_neg_nat,alt_zero,
      cs.wordProd_nil,h1,add_zero]
  · rw [lower_length_fiber cs c hc,
      Finset.sum_pair (indexWord_pos_ne_neg cs (by omega) hc)]

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem maximal_or_unbounded (cs : CoxeterSystem M W) :
    (∃ w, ∀ z, cs.length z ≤ cs.length w) ∨ (∀ n : ℕ, ∃ w, n ≤ cs.length w) := by
  by_cases hb : BddAbove (Set.range cs.length)
  · have hf : (Set.range cs.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty cs.length).csSup_mem hf
    left
    refine ⟨b,fun z => ?_⟩
    rw [hb]
    exact le_csSup hf.bddAbove (Set.mem_range_self z)
  · right
    intro n
    by_contra h
    push Not at h
    exact hb ⟨n,by rintro m ⟨z,rfl⟩; exact (h z).le⟩

 theorem max_length_positive (cs : CoxeterSystem M W) {w : W}
    (hmax : ∀ z, cs.length z ≤ cs.length w) : 0 < cs.length w := by
  have h := hmax (cs.simple false)
  rw [cs.length_simple] at h
  omega

 theorem goodIndex_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n ≤ cs.length c) : GoodIndex cs (n:ℤ) := by
  intro w hw
  have h := hw c
  have hp := max_length_positive cs hw
  omega

 theorem goodIndex_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n < cs.length c) : GoodIndex cs (-(n:ℤ)) := by
  intro w hw
  have h := hw c
  omega

 theorem exists_good_index (cs : CoxeterSystem M W) (z : W) :
    ∃ i : ℤ, GoodIndex cs i ∧ |i|=(cs.length z:ℤ) ∧ indexWord cs i=z := by
  obtain ⟨i,hi,he⟩ := exists_indexWord cs z
  by_cases hgood : GoodIndex cs i
  · exact ⟨i,hgood,hi,he⟩
  · have hbad : ∃ w, (∀ x, cs.length x ≤ cs.length w) ∧
        ¬(-(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)) := by
      simpa only [GoodIndex,not_forall,exists_prop] using hgood
    obtain ⟨w,hw,hbad⟩ := hbad
    have hl := hw z
    have habs := abs_le.mp (show |i|≤(cs.length w:ℤ) by rw [hi]; exact_mod_cast hl)
    have hi' : i= -(cs.length w:ℤ) := by omega
    have hwz : cs.length w=cs.length z := by rw [hi'] at hi; simpa using hi
    refine ⟨cs.length z,goodIndex_nat cs (c := z) le_rfl,by simp,?_⟩
    have hp := indexWord_period cs (rotation_pow_max cs w hw) (-(cs.length w:ℤ)) 1
    rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)*1=(cs.length w:ℤ) by ring] at hp
    rw [← hwz,hp,← hi',he]

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section

 attribute [local instance] OAI.KLInvariance.SignedDihedral.instDecidable_solutions_1
theorem odd_add_natAbs (i : ℤ) (r : ℕ) : Odd (i+r) ↔ Odd (i.natAbs+r) := by
  rw [Int.odd_iff, Nat.odd_iff]
  have hi := Int.natCast_natAbs i
  obtain h | h := le_total 0 i
  · rw [abs_of_nonneg h] at hi
    omega
  · rw [abs_of_nonpos h] at hi
    omega

 theorem odd_sub_natAbs (i : ℤ) (r : ℕ) : Odd (i-r) ↔ Odd (i.natAbs+r) := by
  rw [← odd_add_natAbs, Int.odd_iff, Int.odd_iff]
  omega

 theorem arrowAfter_pos {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) r =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ 0 < j ∧ j.natAbs < r then 1 else 0 := by
  have hir : |i| < |(r:ℤ)| ↔ i.natAbs < r := by
    rw [Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+r) ↔ 0 < j ∧ j.natAbs < r := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        have he : (j.natAbs : ℤ) = j := (Int.natCast_natAbs j).trans (abs_of_pos hj)
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        omega
    simp only [arrowAfter, hir, odd_add_natAbs, hb]
  · simp only [arrowAfter, hir, hl, false_and, ite_false, if_false]

 theorem arrowAfter_neg {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ (0 < j ∨ r < j.natAbs) then 1 else 0 := by
  have hir : |i| < |-(r:ℤ)| ↔ i.natAbs < r := by
    rw [abs_neg, Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+ -r) ↔ 0 < j ∨ r < j.natAbs := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        have he : (j.natAbs : ℤ) = -j := (Int.natCast_natAbs j).trans (abs_of_neg hj')
        omega
    simp only [arrowAfter, hir, show i+ -(r:ℤ)=i-r by ring, odd_sub_natAbs]
    rw [show i-(r:ℤ) = i+ -r by ring, hb]
    split_ifs <;> rfl
  · simp only [arrowAfter, hir, hl, false_and, ite_false, if_false]

 theorem arrowAfter_next {i j : ℤ} (hij : |i| < |j|) (z : ℤ) :
    arrowAfter j (i+j) z =
      if j.natAbs < z.natAbs ∧ Odd (j.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hlt : |j| < |z| ↔ j.natAbs < z.natAbs := by
    rw [← Int.natCast_natAbs j, ← Int.natCast_natAbs z, Nat.cast_lt]
  have ho : Odd (j+z) ↔ Odd (j.natAbs+z.natAbs) := by
    have hj := Int.natCast_natAbs j
    have hz := Int.natCast_natAbs z
    rw [Int.odd_iff,Nat.odd_iff]
    rcases le_total 0 j with hj'|hj' <;> rcases le_total 0 z with hz'|hz'
    · rw [abs_of_nonneg hj'] at hj
      rw [abs_of_nonneg hz'] at hz
      omega
    · rw [abs_of_nonneg hj'] at hj
      rw [abs_of_nonpos hz'] at hz
      omega
    · rw [abs_of_nonpos hj'] at hj
      rw [abs_of_nonneg hz'] at hz
      omega
    · rw [abs_of_nonpos hj'] at hj
      rw [abs_of_nonpos hz'] at hz
      omega
  by_cases h : |j| < |z|
  · simp only [arrowAfter, before_next_source hij h, ho, hlt]
  · have h' := hlt.not.mp h
    simp only [arrowAfter,h,h',false_and,ite_false, if_false]

 theorem countAfter_base {i j : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) :
    countAfter i (i+j) j = (j.natAbs-i.natAbs-1)/2 := by
  unfold countAfter
  rw [arrowAfter_self,add_zero]
  have hs : ∀ r ∈ Finset.range j.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
        if i.natAbs < r ∧ Odd (i.natAbs+r) then 1 else 0 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    have hn : ¬ j.natAbs < r := by omega
    simp only [hn,and_false,ite_false, if_false,zero_add,hr',or_true,and_true]
  rw [Finset.sum_congr rfl hs, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hh : i.natAbs < j.natAbs := by
    rw [← Nat.cast_lt (α := ℤ),Int.natCast_natAbs,Int.natCast_natAbs]
    exact hij
  have he : j.natAbs = i.natAbs+2*((j.natAbs-i.natAbs-1)/2)+1 := by
    rw [Nat.odd_iff] at ho
    omega
  conv_lhs => rw [he]
  exact eligible_ranks_card _ _

/-- A double internal level together with the singleton top contributes one
outgoing arrow per rank, independently of top parity. -/
 theorem total_outgoing_count (L C : ℕ) (h : L ≤ C) :
    (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then 2 else 0) +
      (if L < C ∧ Odd (L+C) then 1 else 0) = C-L := by
  induction C, h using Nat.le_induction with
  | base =>
    have hz : ∀ r ∈ Finset.range L, ¬ L < r := by
      intro r hr
      have := Finset.mem_range.mp hr
      omega
    have hs : (∑ r ∈ Finset.range L, if L < r ∧ Odd (L+r) then 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp only [hz r hr, false_and, ite_false, if_false]
    simp only [hs, lt_self_iff_false, false_and, ite_false, if_false, add_zero, Nat.sub_self]
  | succ C h ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : L<C
    · have hc' : L<C+1 := by omega
      by_cases he : Odd (L+C)
      · have he' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [hc,he,and_self,ite_true, if_true] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true, if_true,ite_false, if_false,add_zero]
        omega
      · have he' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [he,and_false,ite_false, if_false,add_zero] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true, if_true,ite_false, if_false,add_zero]
        omega
    · have heq : C=L := by omega
      subst C
      have he : ¬Odd (L+L) := by rw [Nat.odd_iff]; omega
      have he' : Odd (L+(L+1)) := by rw [Nat.odd_iff]; omega
      simp only [lt_self_iff_false,false_and,ite_false, if_false,add_zero] at ih
      simp only [he,he',and_false,and_true,ite_false, if_false,Nat.lt_succ_self,ite_true, if_true,add_zero]
      omega

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section

 local instance instDecidable_solutions_2_r36b5c4_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem odd_add_abs (i z : ℤ) : Odd (i+z) ↔ Odd (i.natAbs+z.natAbs) := by
  have hi := Int.natCast_natAbs i
  have hz := Int.natCast_natAbs z
  rw [Int.odd_iff,Nat.odd_iff]
  rcases le_total 0 i with hi'|hi' <;> rcases le_total 0 z with hz'|hz'
  · rw [abs_of_nonneg hi'] at hi
    rw [abs_of_nonneg hz'] at hz
    omega
  · rw [abs_of_nonneg hi'] at hi
    rw [abs_of_nonpos hz'] at hz
    omega
  · rw [abs_of_nonpos hi'] at hi
    rw [abs_of_nonneg hz'] at hz
    omega
  · rw [abs_of_nonpos hi'] at hi
    rw [abs_of_nonpos hz'] at hz
    omega

 theorem arrowAfter_far {i j z : ℤ} (hij : |i| < |j|) (hjz : |j| < |z|) :
    arrowAfter i (i+j) z = if Odd (i.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hiz := hij.trans hjz
  have hb : Before (i+j) (i+z) ↔ 0 < j := by
    by_cases hj : 0 < j
    · rw [before_same_source_pos hij hiz hj]
      rw [abs_of_pos hj] at hjz
      rw [lt_abs] at hjz
      omega
    · have hj' : j < 0 := by
        have := abs_nonneg i
        rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
        omega
      rw [before_same_source_neg hij hiz hj']
      rw [abs_of_neg hj',lt_abs] at hjz
      omega
  simp only [arrowAfter,hiz,true_and,odd_add_abs,hb]

 theorem positiveCount_formula (L M C : ℕ) (hLM : L < M) (ho : Odd (L+M))
    (hMC : M ≤ C) : positiveCount L M C = (M-L-1)/2 + (C-M) := by
  induction C, hMC using Nat.le_induction with
  | base =>
    have he : M = L+2*((M-L-1)/2)+1 := by
      rw [Nat.odd_iff] at ho
      omega
    have hs : (∑ r ∈ Finset.range M,
        if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) =
        (∑ r ∈ Finset.range M, if L < r ∧ Odd (L+r) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hn : ¬ M < r := by have := Finset.mem_range.mp hr; omega
      simp only [hn,ite_false, if_false]
    rw [positiveCount,hs,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [lt_self_iff_false,false_and,ite_false, if_false,add_zero,Nat.sub_self]
    conv_lhs => rw [he]
    exact eligible_ranks_card _ _
  | succ C hMC ih =>
    rw [positiveCount,Finset.sum_range_succ]
    unfold positiveCount at ih
    by_cases h : M<C
    · have h' : M<C+1 := by omega
      have hl : L<C := by omega
      by_cases hc : Odd (L+C)
      · have hc' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true, if_true,ite_false, if_false,add_zero] at ih ⊢
        omega
      · have hc' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true, if_true,ite_false, if_false,add_zero] at ih ⊢
        omega
    · have heq : C=M := by omega
      subst C
      have hc' : ¬Odd (L+(M+1)) := by rw [Nat.odd_iff] at ho ⊢; omega
      simp only [lt_self_iff_false,false_and,ite_false, if_false,add_zero] at ih
      simp only [hLM,ho,hc',and_self,and_false,ite_true, if_true,ite_false, if_false,lt_self_iff_false,add_zero]
      omega

 theorem countAfter_pos_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : 0 < j)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 + (c.natAbs-j.natAbs) := by
  rcases h with rfl|h
  · rw [countAfter_base hij ho,Nat.sub_self,add_zero]
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hLM : i.natAbs < j.natAbs := by
    exact_mod_cast (show (i.natAbs:ℤ) < j.natAbs by simpa only [Int.natCast_natAbs] using hij)
  have hs : ∀ r ∈ Finset.range c.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then (if j.natAbs < r then 2 else 1) else 0 := by
    intro r _
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    simp only [hj,true_or,and_true,true_and]
    by_cases h1 : i.natAbs < r ∧ Odd (i.natAbs+r)
    · obtain ⟨h1,h2⟩ := h1
      simp only [h1,h2,true_and,ite_true, if_true]
      split_ifs <;> rfl
    · have hh : ¬(i.natAbs < r ∧ Odd (i.natAbs+r) ∧ j.natAbs < r) := by tauto
      simp only [h1,hh,ite_false, if_false,add_zero]
  rw [countAfter,Finset.sum_congr rfl hs,arrowAfter_far hij h]
  simp only [hj,and_true]
  have heq : (if Odd (i.natAbs+c.natAbs) then 1 else 0) =
      (if j.natAbs < c.natAbs ∧ Odd (i.natAbs+c.natAbs) then 1 else 0) := by
    simp only [hMC,true_and]
  rw [heq]
  exact positiveCount_formula _ _ _ hLM ho hMC.le

 theorem countAfter_neg_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : j < 0)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 := by
  rcases h with rfl|h
  · exact countAfter_base hij ho
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hn : ¬0<j := by omega
  have hs : (∑ r ∈ Finset.range c.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) =
      (∑ r ∈ Finset.range j.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hMC.le)
    intro r _ hr
    have hr' : ¬ r < j.natAbs := by simpa only [Finset.mem_range] using hr
    rw [arrowAfter_pos hij,arrowAfter_neg hij]
    simp only [hn,hr',false_or,and_false,false_and,ite_false, if_false,add_zero]
  rw [countAfter,hs,arrowAfter_far hij h]
  simp only [hn,and_false,ite_false, if_false,add_zero]
  have hh := countAfter_base hij ho
  rw [countAfter,arrowAfter_self,add_zero] at hh
  exact hh

 theorem countAfter_next_formula {i j c : ℤ} (hij : |i| < |j|)
    (h : c=j ∨ |j| < |c|) :
    countAfter j (i+j) c = if 0<j then c.natAbs-j.natAbs else 0 := by
  have hMC : j.natAbs ≤ c.natAbs := by
    rcases h with rfl|h
    · exact le_rfl
    · exact_mod_cast (show (j.natAbs:ℤ) ≤ c.natAbs by simpa only [Int.natCast_natAbs] using h.le)
  unfold countAfter
  simp_rw [arrowAfter_next hij]
  simp only [Int.natAbs_natCast,Int.natAbs_neg]
  by_cases hj : 0<j
  · simp only [hj,and_true,ite_true, if_true]
    have hs : ∀ r ∈ Finset.range c.natAbs,
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) +
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) =
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 2 else 0) := by
      intro r _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl hs]
    exact total_outgoing_count _ _ hMC
  · simp only [hj,and_false,ite_false, if_false,add_zero,Finset.sum_const_zero]

/-- The signed-index cardinality identity for the source's forward angular
order. Its identification with actual Coxeter angular roots is separate. -/
 theorem countAfter_difference {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = countAfter j (i+j) c + (j.natAbs-i.natAbs-1)/2 := by
  rw [countAfter_next_formula hij h]
  by_cases hj : 0<j
  · rw [ite_eq_left hj,countAfter_pos_formula hij ho hj h,Nat.add_comm]
  · have hj' : j<0 := by
      have := abs_nonneg i
      rw [abs_of_nonpos (by omega : j≤0)] at hij
      omega
    rw [ite_eq_right hj,zero_add,countAfter_neg_formula hij ho hj' h]

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem natAbs_lt_iff (i j : ℤ) : i.natAbs<j.natAbs ↔ |i| < |j| := by
  rw [← Int.natCast_natAbs,← Int.natCast_natAbs]
  exact (Nat.cast_lt (α := ℤ)).symm

 theorem index_step_iff (cs : CoxeterSystem M W) {i j : ℤ}
    (hi : cs.length (indexWord cs i)=i.natAbs)
    (hj : cs.length (indexWord cs j)=j.natAbs) :
    BruhatStep cs (indexWord cs i) (indexWord cs j) ↔ |i| < |j| ∧ Odd (i+j) := by
  rw [step_iff_odd,hi,hj,natAbs_lt_iff]
  apply and_congr_right
  intro h
  have hnat := (natAbs_lt_iff i j).mpr h
  rw [SignedDihedral.odd_add_abs,Nat.odd_iff,Nat.odd_iff]
  omega

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_3
theorem edgeRoot_same_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hxz : BruhatStep B.system (indexWord B.system i) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hxz) ↔
      SignedDihedral.Before (i+j) (i+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hiz := (index_step_iff B.system hi hz).mp hxz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hiz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hxz hij.2 hiz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_same (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hiz.1 (gj w hw) (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hxz hij.2 hiz.2 hlabel hlabel'

 theorem edgeRoot_next_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hyz : BruhatStep B.system (indexWord B.system j) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      SignedDihedral.Before (i+j) (j+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hjz := (index_step_iff B.system hj hz).mp hyz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hjz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hyz hij.2 hjz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_next (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hjz.1 (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hyz hij.2 hjz.2 hlabel hlabel'

 theorem afterIndicator_one (x : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    B.afterIndicator x α 1=0 := by
  have hn : ¬BruhatStep B.system x 1 := by
    intro h
    have := h.1
    rw [B.system.length_one] at this
    omega
  simp only [afterIndicator,dite_eq_right hn]

 theorem afterIndicator_same {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter i (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system i) (indexWord B.system z)
  · have hs := (index_step_iff B.system hi hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_same_table hxy hstep hi hj hz gj gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hi hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

 theorem afterIndicator_next {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter j (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system j) (indexWord B.system z)
  · have hs := (index_step_iff B.system hj hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_next_table hxy hstep hi hj hz gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hj hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem laterCount_same {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gj : GoodIndex B.system j) (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter i (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_same hxy hi hj hk gj gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_same hxy hi hj hp' gj (goodIndex_nat B.system hnc.le),
    B.afterIndicator_same hxy hi hj hm' gj (goodIndex_neg_nat B.system hnc)]

 theorem laterCount_next {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter j (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_next hxy hi hj hk gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_next hxy hi hj hp' (goodIndex_nat B.system hnc.le),
    B.afterIndicator_next hxy hi hj hm' (goodIndex_neg_nat B.system hnc)]


 theorem laterCount_difference {x y c : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyc : BruhatLE B.system y c) :
    B.laterCount x (B.edgeRoot hxy) c = B.laterCount y (B.edgeRoot hxy) c +
      (B.system.length y-B.system.length x-1)/2 := by
  obtain ⟨i,_,hi,he⟩ := exists_good_index B.system x
  obtain ⟨j,gj,hj,hf⟩ := exists_good_index B.system y
  have hi' : i.natAbs=B.system.length x := by
    exact_mod_cast (show (i.natAbs:ℤ)=(B.system.length x:ℤ) by rw [Int.natCast_natAbs,hi])
  have hj' : j.natAbs=B.system.length y := by
    exact_mod_cast (show (j.natAbs:ℤ)=(B.system.length y:ℤ) by rw [Int.natCast_natAbs,hj])
  obtain ⟨k,gk,hk,hg,hcomp⟩ : ∃ k : ℤ, GoodIndex B.system k ∧
      k.natAbs=B.system.length c ∧ indexWord B.system k=c ∧
      (k=j ∨ |j| < |k|) := by
    by_cases h : c=y
    · subst c
      exact ⟨j,gj,hj',hf,Or.inl rfl⟩
    · obtain ⟨k,gk,hk,hg⟩ := exists_good_index B.system c
      have hlen := length_lt_of_bruhat_ne B.system hyc (Ne.symm h)
      refine ⟨k,gk,?_,hg,Or.inr ?_⟩
      · exact_mod_cast (show (k.natAbs:ℤ)=(B.system.length c:ℤ) by rw [Int.natCast_natAbs,hk])
      · rw [hj,hk]
        exact_mod_cast hlen
  have ilen : B.system.length (indexWord B.system i)=i.natAbs := by rw [he,hi']
  have jlen : B.system.length (indexWord B.system j)=j.natAbs := by rw [hf,hj']
  have klen : B.system.length (indexWord B.system k)=k.natAbs := by rw [hg,hk]
  subst x y c
  rw [B.laterCount_same hxy ilen jlen klen gj gk,
    B.laterCount_next hxy ilen jlen klen gk,ilen,jlen]
  have hs := (index_step_iff B.system ilen jlen).mp hxy
  exact SignedDihedral.countAfter_difference hs.1
    ((SignedDihedral.odd_add_abs i j).mp hs.2) hcomp

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem afterIndicator_eq_zero {x z : planeSubgroup M cs P}
    (α : PositiveRoot M cs) (h : ¬BruhatLE B.system x z) :
    B.afterIndicator x α z = 0 := by
  have hn : ¬BruhatStep B.system x z := fun hz => h (Relation.ReflTransGen.single hz)
  simp only [afterIndicator,dite_eq_right hn]

/-- Counting only the relative interval above a lower bound does not alter
an outgoing count based at a vertex above that bound. -/
 theorem interval_laterCount {a x c : planeSubgroup M cs P}
    (hax : BruhatLE B.system a x) (α : PositiveRoot M cs) :
    (∑ᶠ z : Interval B.system a c, B.afterIndicator x α z.val) =
      B.laterCount x α c := by
  classical
  let := interval_finite B.system a c
  let : Fintype (Interval B.system a c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype,laterCount]
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (Interval B.system a c)))
    ((lowerFinset B.system c).filter (fun z => BruhatLE B.system a z))
    (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm)
    (fun z => B.afterIndicator x α z)
  refine hs.symm.trans (Finset.sum_subset (Finset.filter_subset _ _) ?_)
  intro z hz hn
  apply B.afterIndicator_eq_zero
  intro hxz
  exact hn (Finset.mem_filter.mpr ⟨hz,bruhat_trans B.system hax hxz⟩)

 theorem edgeRoot_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    B.edgeRoot hxy = graphRoot ((B.coset_step_iff hmin x y).mpr hxy) := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  change (y:W)*(x:W)⁻¹=((y:W)*a₀)*((x:W)*a₀)⁻¹
  group

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P' : Submodule ℝ (I' → ℝ)} (B' : PlaneBasis (M := M') (cs := cs') P')

/-- A full relative interval transport carries the actual angular later-edge
count. An arbitrary graph embedding would not suffice here. -/
 theorem interval_map_count {a c : planeSubgroup M cs P}
    (hac : BruhatLE B.system a c)
    (F : Interval B.system a c → planeSubgroup M' cs' P')
    (hinj : Function.Injective F)
    (hrange : Set.range F = {z | BruhatLE B'.system (F ⟨a,bruhat_refl B.system a,hac⟩) z ∧
      BruhatLE B'.system z (F ⟨c,hac,bruhat_refl B.system c⟩)})
    (x : Interval B.system a c) (α : PositiveRoot M' cs') :
    (∑ᶠ z : Interval B.system a c, B'.afterIndicator (F x) α (F z)) =
      B'.laterCount (F x) α (F ⟨c,hac,bruhat_refl B.system c⟩) := by
  classical
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hmem (z : Interval B.system a c) : BruhatLE B'.system (F lo) (F z) ∧
      BruhatLE B'.system (F z) (F hi) := by
    exact (Set.ext_iff.mp hrange (F z)).mp ⟨z,rfl⟩
  let f : Interval B.system a c → Interval B'.system (F lo) (F hi) :=
    fun z => ⟨F z,hmem z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact hinj (congrArg Subtype.val h)
    · intro z
      obtain ⟨w,hw⟩ := (Set.ext_iff.mp hrange z.val).mpr z.property
      exact ⟨w,Subtype.ext hw⟩
  let E := Equiv.ofBijective f hf
  have hs := finsum_comp_equiv E (f := fun z : Interval B'.system (F lo) (F hi) =>
    B'.afterIndicator (F x) α z.val)
  exact hs.trans (B'.interval_laterCount (hmem x).1 α)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

 theorem ambientAfterIndicator_of_le {x z : W} (α : PositiveRoot M cs)
    (hz : BruhatLE cs z x) : ambientAfterIndicator x α z=0 := by
  classical
  have hn : ¬BruhatStep cs x z := fun h =>
    (not_lt_of_ge (length_le_of_bruhat cs hz)) h.1
  simp only [ambientAfterIndicator,dite_eq_right hn]

 theorem ambientAfterIndicator_edge_self {x y : W} (hxy : BruhatStep cs x y) :
    ambientAfterIndicator x (graphRoot hxy) y=0 := by
  classical
  simp only [ambientAfterIndicator,dite_eq_left hxy,lt_self_iff_false,ite_false, if_false]

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

 theorem ambientAfterIndicator_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (x z : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    ambientAfterIndicator ((x:W)*a₀) α ((z:W)*a₀) = B.afterIndicator x α z := by
  classical
  by_cases h : BruhatStep B.system x z
  · have h' := (B.coset_step_iff hmin x z).mpr h
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_left h,dite_eq_left h',B.edgeRoot_coset hmin h]
  · have h' : ¬BruhatStep cs ((x:W)*a₀) ((z:W)*a₀) :=
      fun hz => h ((B.coset_step_iff hmin x z).mp hz)
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_right h,dite_eq_right h']

universe u' v'
variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}


 theorem transported_count_difference {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hrank : B.system.length a+2 ≤ B.system.length c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  dsimp only
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  obtain ⟨P',B',a',F,hmin',hinj,hcoord,horder,hstep,hlen,hrange⟩ :=
    B.transport_interval hmin hac hrank hlo hhi e
  have hFxy : BruhatStep B'.system (F lo) (F y) := (hstep lo y).mpr hxy
  have hFyc : BruhatLE B'.system (F y) (F hi) := (horder y hi).mpr y.property.2
  have hroot : B'.edgeRoot hFxy=graphRoot hedge := by
    rw [B'.edgeRoot_coset hmin' hFxy]
    unfold graphRoot
    apply congrArg (positiveRoot M' cs')
    apply Subtype.ext
    change ((F y:W')*a')*((F lo:W')*a')⁻¹=(e (inc y)).val*(e (inc lo)).val⁻¹
    rw [hcoord y,hcoord lo]
  have hsum (x : Interval B.system a c) :
      (∑ᶠ z : Interval B.system a c,
        ambientAfterIndicator (e (inc x)).val (graphRoot hedge) (e (inc z)).val) =
      B'.laterCount (F x) (B'.edgeRoot hFxy) (F hi) := by
    rw [← B.interval_map_count B' hac F hinj hrange x (B'.edgeRoot hFxy)]
    apply finsum_congr
    intro z
    rw [← hcoord x,← hcoord z,← hroot]
    exact B'.ambientAfterIndicator_coset hmin' (F x) (F z) _
  rw [hsum lo,hsum y,B'.laterCount_difference hFxy hFyc]
  congr 1
  have hy := hlen y
  change B'.system.length (F y)+B.system.length a =
    B'.system.length (F lo)+B.system.length y.val at hy
  omega

/-- The same scheduled count with no restriction on the relative rank. -/
 theorem transported_count_difference_all {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  by_cases hrank : B.system.length a+2 ≤ B.system.length c
  · exact B.transported_count_difference hmin hac hrank hlo hhi e y hxy
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  have hylen := hxy.1
  have hyc := length_le_of_bruhat B.system y.property.2
  have hlen : B.system.length y.val=B.system.length a+1 := by omega
  have heyc : y.val=c := by
    by_contra hn
    have hlt := length_lt_of_bruhat_ne B.system y.property.2 hn
    omega
  have hverts (z : Interval B.system a c) : z=lo ∨ z=y := by
    by_cases hz : z.val=a
    · exact Or.inl (Subtype.ext hz)
    · right
      apply Subtype.ext
      rw [heyc]
      by_contra hzc
      have hzlo := length_lt_of_bruhat_ne B.system z.property.1 (Ne.symm hz)
      have hzhi := length_lt_of_bruhat_ne B.system z.property.2 hzc
      omega
  have hzero₁ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
    · exact ambientAfterIndicator_edge_self hedge
  have hzero₂ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (Relation.ReflTransGen.single hedge)
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
  rw [hzero₁,hzero₂,hlen]
  omega

end PlaneBasis
end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/

section

namespace KLInvariance.SymmetricPlaneIdeal
universe uk uv
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
noncomputable section

 theorem ideal_span_eq (s : Set V) :
    ideal (Submodule.span k s) = Ideal.span ((SymmetricAlgebra.ι k V) '' s) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨x,hx,rfl⟩
    | zero =>
      rw [map_zero]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul,Algebra.smul_def]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).mul_mem_left _ hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact (ι_mem_iff _ _).mpr (Submodule.subset_span hv)

end
end KLInvariance.SymmetricPlaneIdeal

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {B C : Sheaf.{u,v,w,z} (R := R) G}


theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)] :
    ∃ D : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  let := hC.free O x
  let := hC.finite O x
  obtain ⟨g,jv,hfree,hfinite,hjv⟩ := (j.above x hmax).extend_stalk
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  let := hfinite
  let n := Module.finrank R (LinearMap.ker g)
  let S : Sheaf.{u,v,w,z} (R := R) G := pi (fun _ : Fin n => O.sheaf x)
  let jq : LinearMap.ker g ≃ₗ[R] S.vertex x :=
    (Module.finBasis R (LinearMap.ker g)).equivFun.trans
      (LinearEquiv.piCongrRight (fun _ : Fin n => O.top x)).symm
  let jv' : B.vertex x ≃ₗ[R] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl R (C.vertex x)) jq)
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) :=
    pi_subsingleton_vertex _ y (fun _ => O.support x y (fun hyx => hx (hU hyx hy)))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    apply pi_subsingleton_edge
    intro i
    let := O.support x (G.target e) (fun h => hx (hU h he))
    exact (O.quotient x e).1.subsingleton
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hq : (prod C S).UpperQuotient α :=
    prod_upperQuotient C S α (hC.quotient O) (pi_upperQuotient _ α (fun _ => O.quotient x))
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = (prod C S).lower e (castStalkIso B (prod C S) he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact hjv v ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  refine ⟨prod C S,?_,⟨jj.extend hU x hx hmax α hBq hq jv' hout⟩⟩
  exact .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  (B : Sheaf.{u,v,w,z} (R := R) G)

/-- Actual finite descending decomposition over a local ring. This does not
assume that localization preserves indecomposability. Its explicitly stated
rank-one model criteria must be proved before applying it to a root plane. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free R (B.vertex x))
    (hBfinite : ∀ x, Module.Finite R (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated) :
    ∃ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : Sheaf.{u,v,w,z} (R := R) G,
        ModelSum O.sheaf Set.univ D ∧ Nonempty (Iso B D) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU C hC j
      by_cases hs : s = ∅
      · subst s
        have hh : ((∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
        exact ⟨C,hh ▸ hC,⟨OnIso.ofUniv (hh ▸ j)⟩⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        let := hBfinite x
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum O hU hC j hBq hBf hBg x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') D (heq ▸ hD) (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : OnIso B zero (∅ : Set V) :=
    ⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.Sheaf

end


section

/-! The actual plane prime and its localization in the coefficient polynomial
ring of the chosen nondegenerate ambient realization. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem linear_isUnit_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (linearPolynomial basis (embed M a))) ↔ a ∉ P := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (planePrime basis P)]
  change _ ∉ planePrime basis P ↔ _
  rw [linear_mem_planePrime_iff]

end
end KLInvariance.TitsSpace

end


section

/-! The actual finite relative lower ideal in a maximal root-plane coset.
No order-reflection identification with ambient comparability is used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  (a₀ b : W)
noncomputable section

variable (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))

 theorem coset_lift_live (e : Edge cs 1 b)
    (he : label cs 1 b e ∈ planeSubgroup M cs P)
    (x : B.CosetVertex a₀ b) (hx : B.cosetAmbient a₀ b x=source cs 1 b e) :
    ∃ a : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin a=e ∧
      (B.cosetGraph a₀ b).source a=x := by
  let t : planeSubgroup M cs P := ⟨label cs 1 b e,he⟩
  have hy : ((t*x.val : planeSubgroup M cs P):W)*a₀ = (target cs 1 b e).val := by
    change (label cs 1 b e*(x.val:W))*a₀ = _
    rw [mul_assoc,show (x.val:W)*a₀=(source cs 1 b e).val from congrArg Subtype.val hx]
    exact label_mul_source cs 1 b e
  let y : B.CosetVertex a₀ b := ⟨t*x.val,one_bruhat B.system _,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hye : B.cosetAmbient a₀ b y=target cs 1 b e := Subtype.ext hy
  have hs : BruhatStep B.system x.val y.val := by
    apply (B.coset_step_iff hmin _ _).mp
    change BruhatStep cs (B.cosetAmbient a₀ b x).val (B.cosetAmbient a₀ b y).val
    rw [hx,hye]
    exact e.property
  refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
  apply Subtype.ext
  exact Prod.ext hx hye

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Actual plane localization of the boundary-constructed sheaf. Its relative
coset restriction is free, generated and flabby with upper quotient maps;
no character or upward-kernel freeness theorem is used. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem edge_subsingleton_of_unit (α : E → R) (hq : B.UpperQuotient α)
    (e : E) (he : IsUnit (α e)) : Subsingleton (B.edge e) := by
  obtain ⟨a,ha⟩ := he
  have hz : ∀ v : B.edge e, v=0 := by
    intro v
    obtain ⟨w,rfl⟩ := (hq e).1 v
    apply ((hq e).2 w).mpr
    refine ⟨(↑a⁻¹ : R) • w,?_⟩
    rw [← ha,smul_smul]
    simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 omit [Fintype σ] in
 theorem polynomialLabel_unit_iff (e : Edge cs 1 b) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (polynomialLabel cs 1 b basis e)) ↔ label cs 1 b e ∉ planeSubgroup M cs P := by
  change IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (linearPolynomial basis (embed M (BruhatGraph.root cs 1 b e).val))) ↔ _
  rw [linear_isUnit_iff]
  have hr := positiveRoot_represents M cs ⟨label cs 1 b e,label_isReflection cs 1 b e⟩
  exact not_congr (Represents.planeSubgroup_mem_iff M cs hr).symm

 omit [Fintype σ] in
 theorem localizedCoset_quotient (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) :
    (B.localizedCoset basis a₀ b hmin C).UpperQuotient (B.cosetLabel basis a₀ b hmin) :=
  (C.baseChange (PlaneRing basis P)).pullback_quotient (B.cosetGraphMap a₀ b hmin)
    (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialLabel cs 1 b basis e))
    (C.baseChange_upperQuotient (PlaneRing basis P) (polynomialLabel cs 1 b basis) hq)

 omit [Fintype σ] in
 theorem localizedCoset_generated (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hg : C.Generated) : (B.localizedCoset basis a₀ b hmin C).Generated :=
  (C.baseChange (PlaneRing basis P)).pullback_generated _
    (C.baseChange_generated (PlaneRing basis P) hg)

 omit [Fintype σ] in
 theorem localizedCoset_flabby (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) (hf : C.Flabby) :
    (B.localizedCoset basis a₀ b hmin C).Flabby := by
  let := interval_finite cs 1 b
  apply (C.baseChange (PlaneRing basis P)).pullback_flabby_live _
    (C.baseChange_flabby (PlaneRing basis P) hf) (B.cosetAmbient_injective a₀ b)
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · exact B.coset_lift_live a₀ b hmin

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Partial upward kernels of the actual rank-one model, with their embedded
edge images. No character or freeness property of BMP sheaves is assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

 theorem structure_kernel_iff_dvd (x : V) (hx : x ≤ c)
    (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val)))
    (v : (structureSheaf G α c).vertex x) :
    v ∈ (structureSheaf G α c).upwardKernel x F ↔ kernelProduct G α c x F ∣ v ⟨hx⟩ := by
  classical
  constructor
  · intro hv
    apply Finset.prod_dvd_of_isRelPrime hrel
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    have hvv := congrFun (hv e hh.1) ⟨hh.2⟩
    rcases e with ⟨e,he⟩
    subst x
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hvv)
  · intro hv e he
    funext h
    have hh : e ∈ supportedOutgoing G c x F :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,h.down⟩
    have hd : α e.val ∣ v ⟨hx⟩ := (Finset.dvd_prod_of_mem (fun a => α a.val) hh).trans hv
    rcases e with ⟨e,heq⟩
    subst x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)

 theorem structure_kernel_product (x : V) (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val))) :
    (structureSheaf G α c).upwardKernel x F =
      kernelProduct G α c x F • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  by_cases hx : x ≤ c
  · rw [structure_kernel_iff_dvd G α c x hx F hrel]
    constructor
    · rintro ⟨r,hr⟩
      refine ⟨fun _ => r,Submodule.mem_top,?_⟩
      funext h
      exact hr.symm
    · rintro ⟨w,_,hw⟩
      exact ⟨w ⟨hx⟩,(congrFun hw ⟨hx⟩).symm⟩
  · let _ := structureSheaf_support G α c x hx
    constructor
    · intro _
      exact ⟨0,Submodule.mem_top,Subsingleton.elim _ _⟩
    · intro _
      rw [Subsingleton.elim v 0]
      exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

 theorem lower_surjective_of_generated (B : Sheaf (R := R) G) (hg : B.Generated)
    (hu : ∀ e, Function.Surjective (B.upper e)) (e : E) : Function.Surjective (B.lower e) := by
  intro v
  obtain ⟨w,hw⟩ := hu e v
  obtain ⟨s,hs,ht⟩ := hg (G.target e) w
  refine ⟨s (G.source e),?_⟩
  rw [hs e (Set.mem_univ _) (Set.mem_univ _),ht,hw]

variable [DecompositionMonoid R] [Fintype E] (α : E → R) (c : V)

 theorem structure_lower_image (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (hrel : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.source e) F).map ((structureSheaf G α c).lower e) =
      kernelProduct G α c (G.source e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  apply LinearMap.range_eq_top.mpr
  exact lower_surjective_of_generated _ (structureSheaf_generated G α c)
    (fun a => (structureSheaf_upperQuotient G α c a).1) e

 theorem structure_upper_image (e : E) (F : Set (Outgoing (G := G) (G.target e)))
    (hrel : (supportedOutgoing G c (G.target e) F : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.target e) F).map ((structureSheaf G α c).upper e) =
      kernelProduct G α c (G.target e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  exact LinearMap.range_eq_top.mpr (structureSheaf_upperQuotient G α c e).1

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Distinct prime root labels remain relatively prime after genuine prime
localization. The prime may contain both labels; coprimality here is gcd
coprimality, not comaximality. -/
namespace KLInvariance.LocalizationRelativePrime
variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

omit [IsDomain A] in
 theorem not_dvd_map {a b : A} (ha : Prime a) (hap : a ∈ p) (hab : ¬a ∣ b) :
    ¬ algebraMap A (Localization.AtPrime p) a ∣ algebraMap A (Localization.AtPrime p) b := by
  intro h
  obtain ⟨s,hs,hdiv⟩ := (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_dvd_map.mp h
  rcases ha.dvd_mul.mp hdiv with has | hab'
  · exact hs (p.mem_of_dvd has hap)
  · exact hab hab'

 theorem map_prime {a : A} (ha : Prime a) (hap : a ∈ p) :
    Prime (algebraMap A (Localization.AtPrime p) a) := by
  apply (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_prime ha
  · change algebraMap A (Localization.AtPrime p) a ≠ 0
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective A (Localization.AtPrime p)).ne ha.ne_zero
  · change ¬IsUnit (algebraMap A (Localization.AtPrime p) a)
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ p]
    exact not_not_intro hap

 theorem map_relPrime {a b : A} (ha : Prime a) (hab : ¬a ∣ b) :
    IsRelPrime (algebraMap A (Localization.AtPrime p) a)
      (algebraMap A (Localization.AtPrime p) b) := by
  by_cases hap : a ∈ p
  · exact ((map_prime p ha hap).irreducible.isRelPrime_iff_not_dvd).mpr (not_dvd_map p ha hap hab)
  · exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p a).mpr hap).isRelPrime_left

end KLInvariance.LocalizationRelativePrime

end


section

/-! The local product-kernel lemma on the actual maximal-plane coset.
All regularity hypotheses come from distinct genuine incident reflections. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
open scoped Pointwise
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetEdgeAmbient_injective : Function.Injective (B.cosetEdgeAmbient a₀ b hmin) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.1) h)
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.2) h)

 theorem cosetLabel_relPrime {e f : B.CosetEdge a₀ b} (hef : e ≠ f)
    (hs : (B.cosetGraph a₀ b).source e = (B.cosetGraph a₀ b).source f) :
    IsRelPrime (B.cosetLabel basis a₀ b hmin e) (B.cosetLabel basis a₀ b hmin f) := by
  apply LocalizationRelativePrime.map_relPrime (planePrime basis P)
    (polynomialLabel_prime cs 1 b basis _)
  intro hd
  apply hef
  apply B.cosetEdgeAmbient_injective a₀ b hmin
  apply eq_of_label_source_eq cs 1 b (label_eq_of_polynomialLabel_dvd cs 1 b basis hd)
  exact congrArg (B.cosetAmbient a₀ b) hs

 theorem coset_supported_pairwise [Fintype (B.CosetEdge a₀ b)]
    (c x : B.CosetVertex a₀ b)
    (F : Set (Outgoing (G := B.cosetGraph a₀ b) x)) :
    (supportedOutgoing (B.cosetGraph a₀ b) c x F :
      Set (Outgoing (G := B.cosetGraph a₀ b) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => B.cosetLabel basis a₀ b hmin e.val)) := by
  intro e _ f _ hef
  exact B.cosetLabel_relPrime basis a₀ b hmin
    (fun h => hef (Subtype.ext h)) (e.property.trans f.property.symm)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem outgoing_target_injective (x : B.CosetVertex a₀ b) :
    Function.Injective (fun f : Outgoing (G := B.cosetGraph a₀ b) x => f.val.val.2) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (f.property.trans g.property.symm) h

 theorem supported_card_count [Fintype (B.CosetEdge a₀ b)]
    (φ : Interval cs u b ≃o Interval cs' u' b') (α : PositiveRoot M' cs')
    (a x c : B.CosetVertex a₀ b) (hax : a ≤ x)
    (ha : BruhatLE cs u ((a.val:W)*a₀)) :
    let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
    let inc := B.cosetIntervalMap hmin ha c.property.2
    (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
      ∑ᶠ z : Interval B.system a.val c.val,
        ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val := by
  classical
  let := interval_finite B.system a.val c.val
  let := Fintype.ofFinite (Interval B.system a.val c.val)
  let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
  let inc := B.cosetIntervalMap hmin ha c.property.2
  let F := B.scheduledOutgoing hmin φ α x hx
  let s := supportedOutgoing (B.cosetGraph a₀ b) c x F
  change s.card = ∑ᶠ z : Interval B.system a.val c.val,
    ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val
  rw [finsum_eq_sum_of_fintype]
  rw [show s.card=(∑ _ ∈ s,(1:ℕ)) by simp]
  let idx (f : Outgoing (G := B.cosetGraph a₀ b) x) (hf : f ∈ s) :
      Interval B.system a.val c.val :=
    ⟨f.val.val.2.val,bruhat_trans B.system hax (.single (B.outgoing_step x f)),
      (Finset.mem_filter.mp hf).2.2⟩
  apply Finset.sum_bij_ne_zero (fun f hf _ => idx f hf)
  · intro _ _ _
    exact Finset.mem_univ _
  · intro f hf _ g hg _ h
    have hz : f.val.val.2.val=g.val.val.2.val := congrArg (fun z : Interval B.system a.val c.val => z.val) h
    exact B.outgoing_target_injective x (Subtype.ext hz)
  · intro z _ hz
    have hsz : BruhatStep cs' (φ (B.cosetUpperVertex x hx)).val (φ (inc z)).val := by
      by_contra hn
      exact hz (by simp only [ambientAfterIndicator,dite_eq_right hn])
    have hcz := (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mp hsz
    have hs : BruhatStep B.system x.val z.val := (B.coset_step_iff hmin _ _).mp hcz
    let y : B.CosetVertex a₀ b := ⟨z.val,one_bruhat B.system z.val,
      bruhat_trans cs (B.coset_bruhat hmin z.property.2) c.property.2⟩
    let f : Outgoing (G := B.cosetGraph a₀ b) x := ⟨⟨(x,y),hs⟩,rfl⟩
    have hfF : f ∈ F := by
      change ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val=1
      unfold ambientAfterIndicator at hz ⊢
      split_ifs at hz ⊢ <;> omega
    have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfF,z.property.2⟩
    exact ⟨f,hfs,by omega,rfl⟩
  · intro f hf _
    exact ((Finset.mem_filter.mp hf).2.1).symm

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

/-- The combinatorial factor already constructed from ambient inversion
pairs is exactly the intrinsic relative dihedral edge degree. -/
 theorem planeWeight_coset_edge {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    (planeWeight ((x:W)*a₀) (B.edgeRoot hxy) P).toNat =
      (B.system.length y-B.system.length x-1)/2 := by
  classical
  let α := B.edgeRoot hxy
  obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
    by_cases h : α=B.left
    · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
    · exact ⟨B.left,h,B.left_mem⟩
  have hplane : rootPlane α β=P :=
    (rootPlane_eq_of_mem B.left B.right α β B.distinct
      (B.plane_eq.ge (B.edgeRoot_plane hxy)) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq
  have ha : ¬rootInverted ((x:W)*a₀) α := by
    rw [show α=graphRoot ((B.coset_step_iff hmin x y).mpr hxy) from B.edgeRoot_coset hmin hxy]
    exact graphRoot_not_inverted_source _
  have href : rootRef α=(y:W)*(x:W)⁻¹ :=
    (rootReflection_represents M cs α).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
  have hends : rootRef α*((x:W)*a₀)=(y:W)*a₀ := by rw [href]; group
  have h := planeWeight_relative_degree ((x:W)*a₀) α β hαβ ha
  rw [hplane,hends,B.coset_length_eq hmin x,B.coset_length_eq hmin y] at h
  have hn := planeWeight_nonneg ((x:W)*a₀) α P
  have hlen := hxy.1
  have hc : ((planeWeight ((x:W)*a₀) α P).toNat:ℤ)=planeWeight ((x:W)*a₀) α P :=
    Int.toNat_of_nonneg hn
  change (planeWeight ((x:W)*a₀) α P).toNat = _
  omega

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledLower_self (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) ∉ B.scheduledLower hmin φ e hx := by
  change ambientAfterIndicator _ (graphRoot _) _ ≠ 1
  rw [ambientAfterIndicator_edge_self]
  omega

 theorem supported_count_difference [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) (hyc : e.val.2 ≤ c) :
    (supportedOutgoing (B.cosetGraph a₀ b) c e.val.1 (B.scheduledLower hmin φ e hx)).card =
      (supportedOutgoing (B.cosetGraph a₀ b) c e.val.2 (B.scheduledUpper hmin φ e hx)).card+
        (planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat := by
  let x := e.val.1
  let y := e.val.2
  let α := B.mappedCosetRoot hmin φ e hx
  have hxy : BruhatLE B.system x.val y.val := .single e.property
  have hxc : BruhatLE B.system x.val c.val := bruhat_trans B.system hxy hyc
  let yy : Interval B.system x.val c.val := ⟨y.val,hxy,hyc⟩
  have h := B.transported_count_difference_all hmin hxc hx c.property.2 φ yy e.property
  rw [B.planeWeight_coset_edge hmin e.property]
  change (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
    (supportedOutgoing (B.cosetGraph a₀ b) c y
      (B.scheduledOutgoing hmin φ α y (B.cosetEdge_target_upper hmin e hx))).card+_
  rw [B.supported_card_count hmin φ α x x c (bruhat_refl B.system x.val) hx,
    B.supported_card_count hmin φ α x y c hxy hx]
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledOutgoing_eq (α : PositiveRoot M' cs')
    (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    B.scheduledOutgoing hmin φ α x hx =
      {f | B.cosetEdgeAmbient a₀ b hmin f.val ∈ ambientLater φ α} := by
  ext f
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=x at hs
  subst s
  change (_=1) ↔ ∃ hh : BruhatLE cs u ((x.val:W)*a₀), _=1
  constructor
  · intro h
    exact ⟨hx,h⟩
  · rintro ⟨_,h⟩
    exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Reduction of a root plane along one root is genuinely one-dimensional.
The scalar comparing two nonparallel reduced roots is a nonzero element of
the original base field, hence a unit after every coefficient localization. -/
namespace KLInvariance.PlaneReduction
universe uk uv ua
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
  {A : Type ua} [CommRing A] [Algebra k A]

 theorem scalar_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) :
    ∃ r : k, r ≠ 0 ∧ l c = r • l b := by
  obtain ⟨s,r,hr⟩ := Submodule.mem_span_pair.mp hc
  have hr0 : r ≠ 0 := by
    intro hz
    apply hca
    rw [← hr,hz,zero_smul,add_zero]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_singleton a))
  refine ⟨r,hr0,?_⟩
  rw [← hr,map_add,map_smul,map_smul,ha,smul_zero,zero_add]

 theorem associated_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) : Associated (l c) (l b) := by
  obtain ⟨r,hr,he⟩ := scalar_reduction l ha hc hca
  rw [he,Algebra.smul_def]
  exact associated_unit_mul_left _ _ ((hr.isUnit).map (algebraMap k A))

end KLInvariance.PlaneReduction

end


section

/-! Actual root labels in the localized edge quotient: every nonparallel
root in a given plane has a reduced label associated to any chosen one. -/
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem localizedReduction_self (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    localizedReduction basis P a a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

 theorem positiveRoot_not_line {a c : PositiveRoot M cs} (hca : c ≠ a) :
    c.val ∉ Submodule.span ℝ ({a.val} : Set (I → ℝ)) := by
  intro h
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp (positiveRoots_independent c a hca)).2 r hr

 theorem localizedReduction_associated (P : Submodule ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) (hc : c.val ∈ rootPlane a b) (hca : c ≠ a) :
    Associated (localizedReduction basis P a.val c.val)
      (localizedReduction basis P a.val b.val) :=
by
  exact @PlaneReduction.associated_reduction ℝ _ (I → ℝ) _ _
    (LocalizedEdgeRing basis P a.val) _ _ (localizedReduction basis P a.val)
    a.val b.val c.val (localizedReduction_self basis P a.val) hc
    (positiveRoot_not_line hca)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem polynomialRoot_homogeneous (a : PositiveRoot M cs) :
    polynomialRoot cs basis a ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialRoot
  rw [← basis.sum_repr (embed M a.val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

omit [Fintype σ] in
 theorem polynomialRoot_prime (a : PositiveRoot M cs) : Prime (polynomialRoot cs basis a) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact a.property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype σ] in
 theorem polynomialRoot_not_dvd {a r : PositiveRoot M cs} (h : r ≠ a) :
    ¬ polynomialRoot cs basis a ∣ polynomialRoot cs basis r := by
  rintro ⟨z,hz⟩
  apply embed_not_rootLine a r h
  apply (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp
  refine ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialRoot] using hz


 theorem edgeFactorLift_homogeneous (x : W) (a : PositiveRoot M cs) :
    edgeFactorLift cs basis x a ∈ polynomialGrading ℝ σ (edgeFactorDegree x a : ℤ) := by
  classical
  have h := SetLike.prod_pow_mem_graded (polynomialGrading ℝ σ)
    (fun _ : (planeWeight x a).support => (1 : ℤ))
    (fun P => polynomialRoot cs basis (planeRoot x a P))
    (fun P => (planeWeight x a P.val).toNat)
    (F := Finset.univ) (fun P _ => polynomialRoot_homogeneous cs basis (planeRoot x a P))
  simpa only [edgeFactorLift,edgeFactorDegree,Nat.cast_sum,nsmul_eq_mul,mul_one] using h

omit [Fintype σ] in
 theorem edgeFactorLift_not_dvd (x : W) (a : PositiveRoot M cs) :
    ¬ polynomialRoot cs basis a ∣ edgeFactorLift cs basis x a := by
  classical
  apply (polynomialRoot_prime cs basis a).not_dvd_finsetProd
  intro P _ h
  exact polynomialRoot_not_dvd cs basis (planeRoot_ne x a P)
    ((polynomialRoot_prime cs basis a).dvd_of_dvd_pow h)

variable (u b : W) (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)

theorem rootRef_root (e : Edge cs u b) :
    rootRef (root cs u b e) = label cs u b e :=
  congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨label cs u b e,label_isReflection cs u b e⟩)

 theorem root_not_inverted (e : Edge cs u b) :
    ¬ rootInverted (source cs u b e).val (root cs u b e) := by
  intro h
  have hi := ((rootReflection_represents M cs (root cs u b e)).inversion_iff
    (root cs u b e).property.2 (source cs u b e).val).mp h
  have hl := hi.2
  change cs.length (rootRef (root cs u b e) * (source cs u b e).val) <
    cs.length (source cs u b e).val at hl
  rw [rootRef_root, label_mul_source] at hl
  exact (not_lt_of_ge e.property.1.le) hl

 theorem edgeFactorDegree_edge (e : Edge cs u b) :
    2 * (edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) =
      (cs.length (target cs u b e).val : ℤ) - cs.length (source cs u b e).val - 1 := by
  rw [edgeFactorDegree_cast]
  have h := sum_planeWeight (source cs u b e).val (root cs u b e)
    (root_not_inverted cs u b e)
  rwa [rootRef_root, label_mul_source] at h

 theorem edgeFactorMap_graded (e : Edge cs u b) (n : ℤ) (v : B.sheaf.edge e)
    (hv : v ∈ (B.sheaf.edge e).piece n) :
    edgeFactorMap cs basis u b hub B e v ∈ (B.sheaf.edge e).piece
      (n + edgeFactorDegree (source cs u b e).val (root cs u b e)) := by
  simpa only [edgeFactorMap,LinearMap.lsmul_apply,vadd_eq_add,add_comm] using
    SetLike.GradedSMul.smul_mem (edgeFactorLift_homogeneous cs basis
      (source cs u b e).val (root cs u b e)) hv

omit [Fintype σ] in
 theorem edgeFactorLift_regular (e : Edge cs u b) :
    Function.Injective (fun v : B.sheaf.edge e =>
      edgeFactorLift cs basis (source cs u b e).val (root cs u b e) • v) := by
  let := B.free ((graph cs u b).target e)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target e)))
    (B.sheaf.upper e).map (B.quotient e).1
    (polynomialLabel cs u b basis e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))
    (polynomialLabel_prime cs u b basis e)
    (edgeFactorLift_not_dvd cs basis (source cs u b e).val (root cs u b e)) (B.quotient e).2

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.LocalProducts
open scoped Pointwise
universe ur us um
variable {R : Type ur} [CommRing R] {S : Type us} [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

 theorem smul_top_le_of_map_dvd {p q : R} (h : algebraMap R S q ∣ algebraMap R S p) :
    p • (⊤ : Submodule R M) ≤ q • (⊤ : Submodule R M) := by
  intro z hz
  obtain ⟨w,_,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  obtain ⟨t,ht⟩ := h
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨t • w,Submodule.mem_top,?_⟩
  rw [← IsScalarTower.algebraMap_smul S q,← IsScalarTower.algebraMap_smul S p,
    smul_smul,← ht]

 theorem smul_top_eq_of_map_associated {p q : R}
    (h : Associated (algebraMap R S p) (algebraMap R S q)) :
    p • (⊤ : Submodule R M) = q • (⊤ : Submodule R M) :=
  le_antisymm (smul_top_le_of_map_dvd h.symm.dvd) (smul_top_le_of_map_dvd h.dvd)

variable {ι κ : Type*}

 theorem associated_prod_power (s : Finset ι) (a : ι → S) (p : S)
    (h : ∀ i ∈ s, Associated (a i) p) : Associated (∏ i ∈ s, a i) (p^s.card) := by
  simpa only [Finset.prod_const] using Associated.prod s a (fun _ => p) h

 theorem associated_prod_scale (s : Finset ι) (t : Finset κ) (a : ι → S) (b : κ → S)
    (p f : S) (k : ℕ) (ha : ∀ i ∈ s, Associated (a i) p)
    (hb : ∀ j ∈ t, Associated (b j) p) (hf : Associated f (p^k))
    (hcount : s.card=t.card+k) :
    Associated (∏ i ∈ s, a i) (f*∏ j ∈ t, b j) := by
  have hs := associated_prod_power s a p ha
  have ht := associated_prod_power t b p hb
  apply hs.trans
  have hpow : p^s.card=p^k*p^t.card := by rw [hcount,add_comm,pow_add]
  rw [hpow]
  exact (hf.mul_mul ht).symm

end KLInvariance.LocalProducts

end


section

namespace KLInvariance.TitsSpace
open Module BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem polynomialRoot_reduced (P : Submodule ℝ (I → ℝ)) (a c : PositiveRoot M cs) :
    algebraMap (PlaneRing basis P) (LocalizedEdgeRing basis P a.val)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis c)) =
      localizedReduction basis P a.val c.val := rfl

 theorem planeRoot_outside {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    (planeRoot x a Q).val ∉ rootPlane a b := by
  intro h
  apply hQ
  rw [← planeRoot_plane x a Q]
  exact rootPlane_eq_of_mem a b a (planeRoot x a Q) hab
    (Submodule.subset_span (Set.mem_insert _ _)) h (planeRoot_ne x a Q).symm

 theorem reduced_planeRoot_other_isUnit {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    IsUnit (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val) := by
  have h := (linear_isUnit_iff basis (rootPlane a b) (planeRoot x a Q).val).mpr
    (planeRoot_outside hab Q hQ)
  exact h.map (algebraMap (PlaneRing basis (rootPlane a b))
    (LocalizedEdgeRing basis (rootPlane a b) a.val))

/-- The actual integral edge factor reduces, in each actual plane, to precisely
its plane weight. All other factors are proven units, not discarded formally. -/
 theorem edgeFactor_local_associated (x : W) (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Associated
      (algebraMap (PlaneRing basis (rootPlane a b)) (LocalizedEdgeRing basis (rootPlane a b) a.val)
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis (rootPlane a b)) (edgeFactorLift cs basis x a)))
      ((localizedReduction basis (rootPlane a b) a.val b.val)^((planeWeight x a (rootPlane a b)).toNat)) := by
  classical
  let p := localizedReduction basis (rootPlane a b) a.val b.val
  have hfactor (Q : (planeWeight x a).support) :
      Associated
        ((localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
        (if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) := by
    by_cases hQ : Q.val=rootPlane a b
    · rw [ite_eq_left hQ]
      have hc : (planeRoot x a Q).val ∈ rootPlane a b := by
        rw [← hQ,← planeRoot_plane x a Q]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h := localizedReduction_associated basis (rootPlane a b) a b (planeRoot x a Q)
        hc (planeRoot_ne x a Q)
      simpa only [hQ] using (Associated.pow_pow (M := LocalizedEdgeRing basis (rootPlane a b) a.val) h (n := (planeWeight x a Q.val).toNat))
    · rw [ite_eq_right hQ]
      exact associated_one_iff_isUnit.mpr ((reduced_planeRoot_other_isUnit basis hab Q hQ).pow _)
  have hprod := Associated.prod Finset.univ
    (fun Q : (planeWeight x a).support =>
      (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
    (fun Q => if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1)
    (fun Q _ => hfactor Q)
  have hp : (∏ Q : (planeWeight x a).support,
      if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) =
      p^((planeWeight x a (rootPlane a b)).toNat) := by
    rw [Fintype.prod_ite_eq_ite_exists _ (fun i j hi hj => Subtype.ext (hi.trans hj.symm))]
    by_cases hP : rootPlane a b ∈ (planeWeight x a).support
    · rw [ite_eq_left ⟨⟨rootPlane a b,hP⟩,rfl⟩]
    · have hz := Finsupp.notMem_support_iff.mp hP
      rw [hz,Int.toNat_zero,pow_zero]
      split_ifs <;> rfl
  rw [hp] at hprod
  simpa only [edgeFactorLift,map_prod,map_pow,polynomialRoot_reduced] using hprod

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetRoot_eq (e : B.CosetEdge a₀ b) :
    BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)=B.edgeRoot e.property := by
  rw [B.edgeRoot_coset hmin e.property]
  rfl

 theorem cosetLabel_eq_root (e : B.CosetEdge a₀ b) :
    B.cosetLabel basis a₀ b hmin e=localizedLinear basis P (B.edgeRoot e.property).val := by
  change algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialRoot cs basis (BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)))=_
  rw [B.cosetRoot_eq a₀ b hmin e]
  rfl

 theorem cosetLabel_reduction_associated (e f : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hplane : rootPlane (B.edgeRoot e.property) β=P)
    (hne : B.edgeRoot f.property ≠ B.edgeRoot e.property) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (B.cosetLabel basis a₀ b hmin f))
      (B.reducedCosetRoot basis a₀ b hmin e β) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e,B.cosetLabel_eq_root basis a₀ b hmin f]
  exact localizedReduction_associated basis P (B.edgeRoot e.property) β (B.edgeRoot f.property)
    (hplane.symm ▸ B.edgeRoot_plane f.property) hne

 theorem cosetFactor_reduction_associated (e : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hab : B.edgeRoot e.property ≠ β)
    (hplane : rootPlane (B.edgeRoot e.property) β=P) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
          (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))))
      ((B.reducedCosetRoot basis a₀ b hmin e β)^((planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat)) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e]
  have h := edgeFactor_local_associated basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) β hab
  rw [hplane] at h
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem exists_coset_edge {b : W} (e : Edge cs 1 b)
    (he : (BruhatGraph.root cs 1 b e).val ∈ P) :
    ∃ a₀, ∃ hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀),
      ∃ d : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin d=e := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P (source cs 1 b e).val
  have ht : label cs 1 b e ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs
      ⟨label cs 1 b e,label_isReflection cs 1 b e⟩)).mpr he
  let gg : planeSubgroup M cs P := ⟨g,hg⟩
  let hh : planeSubgroup M cs P := ⟨label cs 1 b e*g,(planeSubgroup M cs P).mul_mem ht hg⟩
  have hy : (hh:W)*a₀=(target cs 1 b e).val := by
    change (label cs 1 b e*g)*a₀=_
    rw [mul_assoc,← hx,label_mul_source]
  let x : B.CosetVertex a₀ b := ⟨gg,one_bruhat B.system gg,hx ▸ (source cs 1 b e).property.2⟩
  let y : B.CosetVertex a₀ b := ⟨hh,one_bruhat B.system hh,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hs : BruhatStep B.system gg hh := by
    apply (B.coset_step_iff hmin gg hh).mp
    rw [show (gg:W)*a₀=(source cs 1 b e).val from hx.symm,hy]
    exact e.property
  refine ⟨a₀,hmin,⟨(x,y),hs⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx.symm) (Subtype.ext hy)

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')

 theorem mappedCosetRoot_eq (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    B.mappedCosetRoot hmin φ e hx = mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin e) hx := rfl

end
end KLInvariance.TitsSpace.PlaneBasis

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/

section

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_6
omit [Fintype I] in
 theorem transportedSchedule_nodup : (transportedSchedule φ).Nodup := by
  unfold transportedSchedule
  exact sortedSchedule_nodup _ _

omit [Fintype I] in
 theorem transportedSchedule_full (e : Edge cs u b) : e ∈ transportedSchedule φ := by
  let := Fintype.ofFinite (Edge cs u b)
  unfold transportedSchedule
  exact (mem_sortedSchedule _ _ _).mpr (Finset.mem_univ _)

omit [Fintype I] in
 theorem transportedSchedule_pairwise : (transportedSchedule φ).Pairwise
     (fun e f => transportedScore φ f ≤ transportedScore φ e) := by
  unfold transportedSchedule
  exact sortedSchedule_pairwise _ _

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

/-! Strict later-label membership in a finite nondecreasing schedule,
with arbitrary positions for equal labels. -/
namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem mem_suffix_iff_score_lt (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b))
    (hq : e::q <:+ p) (hf : f ∈ p) (hne : score e ≠ score f) :
    f ∈ q ↔ score e < score f := by
  obtain ⟨a,rfl⟩ := hq
  have h := List.pairwise_append.mp hs
  constructor
  · intro hfq
    exact lt_of_le_of_ne ((List.pairwise_cons.mp h.2.1).1 f hfq) hne
  · intro hlt
    rcases List.mem_append.mp hf with hfa | hfr
    · exact False.elim (not_le_of_gt hlt (h.2.2 f hfa e List.mem_cons_self))
    · rcases List.mem_cons.mp hfr with rfl | hfr
      · exact False.elim (hne rfl)
      · exact hfr

 theorem mem_suffix_iff_score_lt_injective (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b)) (hn : p.Nodup)
    (hq : e::q <:+ p) (hf : f ∈ p) (heq : score e = score f → e=f) :
    f ∈ q ↔ score e < score f := by
  by_cases hne : score e ≠ score f
  · exact mem_suffix_iff_score_lt score hs hq hf hne
  · have hef := heq (not_ne_iff.mp hne)
    subst f
    have hx := (List.nodup_cons.mp (hn.sublist hq.sublist)).1
    simp only [hx,lt_self_iff_false]

end KLInvariance.SchedulePaths

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem shifted_map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  exact Submodule.mem_map.mpr ⟨component 𝓜 (n-d) w,hS (n-d) w hw,
    (map_component 𝓜 𝓝 f d hf n w).symm⟩

/-- Hilbert series of the actual embedded image of a homogeneous injection. -/
 theorem shifted_image_value
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      q^d * value 𝓜 (S.restrictScalars k) q := by
  have ha := hs.hasSum.mul_left (q^d)
  have hb : HasSum
      (fun n : ℤ => (Module.finrank k (piece 𝓜 (S.restrictScalars k) (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 (S.restrictScalars k) q) := by
    apply (Equiv.addRight d).hasSum_iff.mp
    apply ha.congr_fun
    intro n
    change (Module.finrank k (piece 𝓜 (S.restrictScalars k) (n+d-d)) : ℝ)*q^(n+d) =
      q^d * ((Module.finrank k (piece 𝓜 (S.restrictScalars k) n) : ℝ)*q^n)
    rw [add_sub_cancel_right,zpow_add₀ hq]
    ring
  apply HasSum.tsum_eq
  apply hb.congr_fun
  intro n
  unfold term
  rw [← (subPieceEquiv 𝓝 (S.map f) n).finrank_eq,
    ← (shiftedImagePieceEquiv 𝓜 𝓝 S hS f d hf hinj n).finrank_eq,
    (subPieceEquiv 𝓜 S (n-d)).finrank_eq]

end KLInvariance.Hilbert

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe us um
variable {σ : Type us} [Fintype σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  (B : GradedSheaf (𝓐 := polynomialGrading ℝ σ) G)
noncomputable section

omit [Fintype σ] in
 theorem upperImage_homogeneous (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    ∀ n v, v ∈ B.upperImage e H → component (B.edge e).piece n v ∈ B.upperImage e H :=
  map_homogeneous (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) H) (B.upwardKernel_homogeneous (G.target e) H)
    (B.upper e).map (B.upper e).graded

 theorem kernelHilbert_edge (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      value (B.edge e).piece ((B.lowerImage e F).restrictScalars ℝ) q := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.source e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.source e)).piece
  have h := B.hilbert_edge_increment (G.source e) F ⟨e,rfl⟩ hq
    (summable_term ℝ σ (B.vertex (G.source e)).piece _ hq hq1)
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

 theorem shifted_upperImage_value (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    value (B.edge e).piece (((B.upperImage e H).map φ).restrictScalars ℝ) q =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.target e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.target e)).piece
  rw [shifted_image_value (B.edge e).piece (B.edge e).piece (B.upperImage e H)
    (B.upperImage_homogeneous e H) φ d hφ hφinj hq.ne'
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)]
  rw [show value (B.edge e).piece ((B.upperImage e H).restrictScalars ℝ) q =
    (1-q) * B.kernelHilbert q (G.target e) H from
      B.upper_image_value α hquot e H ha hreg hinj hq
        (summable_term ℝ σ (B.vertex (G.target e)).piece _ hq hq1)]
  exact (mul_assoc _ _ _).symm


 theorem edge_increment_le (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) ≤
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.edge e).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.edge e).piece
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  exact (summable_term ℝ σ (B.edge e).piece _ hq hq1).tsum_le_tsum
    (term_mono (B.edge e).piece hinc hq)
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)

/-- Even a finite-length or higher-codimension embedded defect is detected by
one positive numerical equality. This does not replace the image inclusion. -/
 theorem edge_increment_eq_iff (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H) ↔
      B.lowerImage e F = (B.upperImage e H).map φ := by
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  constructor
  · intro heq
    have h := polynomial_eq_of_value_eq ℝ σ (B.edge e).piece hinc
      (shifted_map_homogeneous (B.edge e).piece (B.edge e).piece (B.upperImage e H)
        (B.upperImage_homogeneous e H) φ d hφ) hq hq1 heq
    ext v
    exact SetLike.ext_iff.mp h v
  · intro heq
    rw [heq]

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section


 theorem actual_edge_increment_le (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.sheaf.kernelHilbert q ((graph cs u b).source e) F -
      B.sheaf.kernelHilbert q ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) ≤
      q^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-q) *
        B.sheaf.kernelHilbert q ((graph cs u b).target e) H := by
  apply B.sheaf.edge_increment_le (polynomialLabel cs u b basis) B.quotient e F H
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact edgeFactorMap_graded cs basis u b hub B e
  · exact edgeFactorLift_regular cs basis u b hub B e
  · exact hinc
  · exact hq
  · exact hq1

 theorem actual_edge_increment_eq_iff (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (B.sheaf.kernelHilbert q ((graph cs u b).source e) F -
      B.sheaf.kernelHilbert q ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) =
      q^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-q) *
        B.sheaf.kernelHilbert q ((graph cs u b).target e) H) ↔
      B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
        (edgeFactorMap cs basis u b hub B e) := by
  apply B.sheaf.edge_increment_eq_iff (polynomialLabel cs u b basis) B.quotient e F H
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact edgeFactorMap_graded cs basis u b hub B e
  · exact edgeFactorLift_regular cs basis u b hub B e
  · exact hinc
  · exact hq
  · exact hq1

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Comparison

/-- Degree-one labels, `q=t²`, and exactly the source degree
`2*k = length(y)-length(x)-1` give the same coefficient at every edge. -/
 theorem edge_scalar_identity {t : ℝ} (ht : t ≠ 0) (m n k : ℤ)
    (h : m + 2*k = n-1) :
    t^m * (t^2)^k * (1-t^2) = (t⁻¹-t) * t^n := by
  have hp : (t^2)^k = t^(2*k) := by
    rw [zpow_mul]
    norm_num
  rw [hp,← zpow_add₀ ht,h]
  have hsub : t^(n-1) = t^n*t⁻¹ := by
    rw [sub_eq_add_neg,zpow_add₀ ht,zpow_neg_one]
  rw [hsub]
  have hcancel : t⁻¹*t=1 := inv_mul_cancel₀ ht
  calc
    t^n*t⁻¹*(1-t^2) = (t⁻¹-t*(t⁻¹*t))*t^n := by ring
    _ = (t⁻¹-t)*t^n := by rw [hcancel,mul_one]

 theorem transferCoefficient_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < t⁻¹-t := by
  have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
  linarith

 theorem stateScale_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (N : ℕ) (m : ℤ) :
    0 < (1-t^2)^N * t^m := by
  have hsq : t^2 < 1 := by nlinarith
  exact mul_pos (pow_pos (sub_pos.mpr hsq) _) (zpow_pos ht _)

/-- Cancellation of a positive state scale converts an additive normalized
edge identity back to its raw Hilbert-series increment. -/
 theorem scaled_increment_eq_iff (a x y k z : ℝ) (ha : a ≠ 0) :
    a*x = a*y+(a*k)*z ↔ x-y=k*z := by
  constructor
  · intro h
    have he : a*x=a*(y+k*z) := by linear_combination h
    have hc := mul_left_cancel₀ ha he
    linarith
  · intro h
    rw [show x=y+k*z by linarith]
    ring

end KLInvariance.Comparison

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype I] in
 theorem stateScale_positive {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : Interval cs u b) : 0 < stateScale (σ := σ) cs u b t x :=
  Comparison.stateScale_pos ht ht1 _ _

 theorem edge_stateScale (e : Edge cs u b) {t : ℝ} (ht : t ≠ 0) :
    stateScale (σ := σ) cs u b t ((graph cs u b).source e) *
      ((t^2)^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-t^2)) =
      (t⁻¹-t) * stateScale (σ := σ) cs u b t ((graph cs u b).target e) := by
  have hd := edgeFactorDegree_edge cs u b e
  have h := Comparison.edge_scalar_identity ht
    ((cs.length (source cs u b e).val : ℤ)-cs.length b)
    ((cs.length (target cs u b e).val : ℤ)-cs.length b)
    (edgeFactorDegree (source cs u b e).val (root cs u b e)) (by omega)
  dsimp only [stateScale,graph]
  calc
    _ = (1-t^2)^(Fintype.card σ) *
        (t^((cs.length (source cs u b e).val : ℤ)-cs.length b) *
          (t^2)^(edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) * (1-t^2)) := by ring
    _ = _ := by rw [h]; ring

/-- A single removal of a later-edge kernel condition has the exact uniform
transfer coefficient `t⁻¹-t` used by the Dyer path matrix. -/
 theorem normalized_edge_increment_le (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    normalizedKernel cs u b basis hub B t ((graph cs u b).source e) F ≤
      normalizedKernel cs u b basis hub B t ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) +
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t ((graph cs u b).target e) H := by
  have h := actual_edge_increment_le cs u b basis hub B e F H hinc
    (sq_pos_of_pos ht) (by nlinarith : t^2 < 1)
  have h' := mul_le_mul_of_nonneg_left h
    (stateScale_positive (σ := σ) cs u b ht ht1 ((graph cs u b).source e)).le
  rw [← mul_assoc,edge_stateScale cs u b e ht.ne',mul_sub] at h'
  simpa only [normalizedKernel,mul_assoc,add_comm] using sub_le_iff_le_add.mp h'

 theorem normalized_edge_increment_eq_iff (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    (hinc : B.sheaf.lowerImage e F ≤ (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (normalizedKernel cs u b basis hub B t ((graph cs u b).source e) F =
      normalizedKernel cs u b basis hub B t ((graph cs u b).source e) (insert ⟨e,rfl⟩ F) +
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t ((graph cs u b).target e) H) ↔
      B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
        (edgeFactorMap cs basis u b hub B e) := by
  rw [← actual_edge_increment_eq_iff cs u b basis hub B e F H hinc
    (sq_pos_of_pos ht) (by nlinarith : t^2 < 1)]
  have hs := (stateScale_positive (σ := σ) cs u b ht ht1 ((graph cs u b).source e)).ne'
  simp only [normalizedKernel]
  rw [← mul_assoc (t⁻¹-t),← edge_stateScale cs u b e ht.ne']
  exact Comparison.scaled_increment_eq_iff _ _ _ _ _ hs

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)
noncomputable section

 omit [Fintype σ] in
 theorem restrictBoundary_kernel (x : Interval cs u b) (T : Set (Edge cs 1 b)) :
    (restrictBoundary cs u b basis hub B).sheaf.upwardSubmodule x
      {e | (upperInclusion cs u b).edge e.val ∈ T} =
    B.sheaf.upwardSubmodule ((upperInclusion cs u b).vertex x) {e | e.val ∈ T} := by
  exact B.sheaf.forget.pullback_kernel (upperInclusion cs u b) x T Set.univ
    (fun e he => False.elim (he (Set.mem_univ e)))
    (fun e _ he => upperInclusion_outgoing cs u b e x he)

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.SchedulePaths
universe u v
variable {V : Type u} {E : Type v}
  (source target : E → V)
noncomputable section

 theorem step_monotone (T : ℝ) (hT : 0 ≤ T) (e : E) :
    Monotone (step source target T e) := by
  intro v w hv x
  dsimp [step]
  split_ifs
  · exact add_le_add (hv x) (mul_le_mul_of_nonneg_left (hv _) hT)
  · simpa using hv x

 theorem step_injective (T : ℝ) (e : E) (hne : source e ≠ target e) :
    Function.Injective (step source target T e) := by
  intro v w he
  have ht := congrFun he (target e)
  simp only [step,hne,ite_false, if_false,add_zero] at ht
  funext x
  have hx := congrFun he x
  dsimp [step] at hx
  split_ifs at hx with h
  · rw [ht] at hx
    exact add_right_cancel hx
  · exact add_right_cancel hx

 theorem dispatch_monotone (T : ℝ) (hT : 0 ≤ T) (p : List E) :
    Monotone (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact monotone_id
  | cons e p ih => exact (step_monotone source target T hT e).comp ih

 theorem dispatch_injective (T : ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e) :
    Function.Injective (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact Function.injective_id
  | cons e p ih =>
    exact (step_injective source target T e (hne e (by simp))).comp
      (ih (fun a ha => hne a (by simp [ha])))

 theorem dispatch_append' (T : ℝ) (v : V → ℝ) (p q : List E) :
    dispatch source target T v (p++q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

/-- A concrete state indexed by the remaining chronological edge list. -/
 theorem remaining_state_le (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q))) :
    D [] ≤ dispatch source target T (D p) p.reverse := by
  induction p with
  | nil => exact le_rfl
  | cons e p ih =>
    have hp := ih (fun a q hq => hstep a q (hq.trans (List.suffix_cons e p)))
    have he := hstep e p (List.suffix_refl _)
    rw [List.reverse_cons,dispatch_append']
    exact hp.trans (dispatch_monotone source target T hT p.reverse he)

/-- If the endpoint bound is equality, every embedded one-edge Hilbert bound
is equality. Injectivity must be used together with the one-sided bounds. -/
 theorem remaining_steps_eq (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q)))
    (hend : D [] = dispatch source target T (D p) p.reverse) :
    ∀ e q, e::q <:+ p → D q = step source target T e (D (e::q)) := by
  induction p with
  | nil =>
    intro e q hq
    have := hq.length_le
    simp at this
  | cons e p ih =>
    have hps := fun a q (hq : a::q <:+ p) => hstep a q (hq.trans (List.suffix_cons e p))
    have hp := remaining_state_le source target T hT D p hps
    have he := hstep e p (List.suffix_refl _)
    have hm := dispatch_monotone source target T hT p.reverse he
    have hend' : D [] = dispatch source target T
        (step source target T e (D (e::p))) p.reverse := by
      simpa only [List.reverse_cons,dispatch_append',dispatch] using hend
    have hh : dispatch source target T (D p) p.reverse =
        dispatch source target T (step source target T e (D (e::p))) p.reverse := by
      apply le_antisymm hm
      exact hend'.symm.le.trans hp
    have hep : D p = step source target T e (D (e::p)) :=
      dispatch_injective source target T p.reverse
        (fun a ha => hne a (by simp only [List.mem_reverse] at ha; simp [ha])) hh
    have hendpoint : D [] = dispatch source target T (D p) p.reverse := by
      exact hend'.trans hh.symm
    intro a q hq
    rcases List.suffix_cons_iff.mp hq with h | h
    · cases h
      exact hep
    · exact ih (fun a ha => hne a (by simp [ha])) hps hendpoint a q h

end
end KLInvariance.SchedulePaths

end


section

namespace KLInvariance.ReverseFiltration
universe ua um un up
variable {A : Type ua} [CommRing A]
  {M : Type um} [AddCommGroup M] [Module A M]
  {N : Type un} [AddCommGroup N] [Module A N]
  {P : Type up} [AddCommGroup P] [Module A P]


 theorem projective_kernel_of_scalar_presentation
    [Module.Projective A M] [Module.Projective A P]
    (f : P →ₗ[A] N) (g : M →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    Module.Projective A (LinearMap.ker f) := by
  let : Module.Projective A (LinearMap.ker g) :=
    Module.Projective.of_equiv (scalarKernelEquiv g a hk ha)
  exact kernel_projective_of_presentation f g hf hg

/-- Scaled equality of two *embedded* images constructs a presentation with
regular scalar kernel. This is the pure module-algebra form of the reverse
freeness step, allowing arbitrary image codimension. -/
 theorem inf_kernel_projective_of_image_eq
    (S : Submodule A M) (T : Submodule A P)
    [Module.Projective A S] [Module.Projective A T]
    (f : M →ₗ[A] N) (g : P →ₗ[A] N) (φ : N →ₗ[A] N)
    (hφ : Function.Injective φ) (himage : S.map f = (T.map g).map φ)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ T → v ∈ T)
    (ha : Function.Injective (fun v : P => a • v)) :
    Module.Projective A ↥(S ⊓ LinearMap.ker f) := by
  let j : T →ₗ[A] S.map f := ((φ.comp g).comp T.subtype).codRestrict (S.map f) (by
    intro v
    rw [himage]
    exact Submodule.mem_map.mpr ⟨g v.val,Submodule.mem_map.mpr ⟨v.val,v.property,rfl⟩,rfl⟩)
  have hj : Function.Surjective j := by
    intro v
    have hv : v.val ∈ (T.map g).map φ := himage ▸ v.property
    obtain ⟨w,hw,hwv⟩ := Submodule.mem_map.mp hv
    obtain ⟨z,hz,hzw⟩ := Submodule.mem_map.mp hw
    exact ⟨⟨z,hz⟩,Subtype.ext ((congrArg φ hzw).trans hwv)⟩
  have hjker (v : T) : j v = 0 ↔ ∃ w : T, v = a • w := by
    constructor
    · intro hv
      have hv' : φ (g v.val) = 0 := congrArg Subtype.val hv
      have hz : g v.val = 0 := hφ (hv'.trans (map_zero φ).symm)
      obtain ⟨w,hw⟩ := (hk v.val).mp hz
      refine ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      apply Subtype.ext
      change φ (g (a • w.val)) = 0
      rw [(hk (a • w.val)).mpr ⟨w.val,rfl⟩,map_zero]
  have haT : Function.Injective (fun v : T => a • v) := by
    intro v w hvw
    exact Subtype.ext (ha (congrArg Subtype.val hvw))
  let : Module.Projective A (LinearMap.ker (Hilbert.imageMap S f)) :=
    projective_kernel_of_scalar_presentation (Hilbert.imageMap S f) j
      (Hilbert.imageMap_surjective S f) hj a hjker haT
  exact Module.Projective.of_equiv (imageMapKernelEquiv S f).symm

end KLInvariance.ReverseFiltration

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
/-- The reverse-freeness step uses precisely the already free upper kernel
and the preceding lower kernel, plus the actual embedded image equality. -/
 theorem partial_kernel_projective_of_image_eq (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)]
    [Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)]
    (heq : B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e)) :
    Module.Projective (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)) := by
  rw [B.sheaf.upwardKernel_insert]
  apply ReverseFiltration.inf_kernel_projective_of_image_eq
    (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)
    (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)
    (B.sheaf.lower e).map (B.sheaf.upper e).map (edgeFactorMap cs basis u b hub B e)
    (edgeFactorLift_regular cs basis u b hub B e) heq
    (polynomialLabel cs u b basis e) (B.quotient e).2
  · apply B.sheaf.upwardSubmodule_saturated
    intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _

 theorem partial_kernel_free_of_image_eq (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).source e)))
    (H : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) F)]
    [Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).target e) H)]
    (heq : B.sheaf.lowerImage e F = (B.sheaf.upperImage e H).map
      (edgeFactorMap cs basis u b hub B e)) :
    Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)) := by
  let D := B.sheaf.upwardKernel ((graph cs u b).source e) (insert ⟨e,rfl⟩ F)
  let : Module.Projective (Coefficient (σ := σ)) D :=
    partial_kernel_projective_of_image_eq cs u b basis hub B e F H heq
  obtain ⟨ι,_,bs,_⟩ := exists_homogeneous_basis_polynomial (k := ℝ) (σ := σ)
    D.piece 0 D.nonneg
  exact Module.Free.of_basis bs

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype I] in
 theorem remainingConditions_cons_source (e : Edge cs u b) (p : List (Edge cs u b)) :
    remainingConditions cs u b (e::p) (source cs u b e) =
      insert ⟨e,rfl⟩ (remainingConditions cs u b p (source cs u b e)) := by
  ext f
  simp only [remainingConditions,Set.mem_ofPred_eq,List.mem_cons,Set.mem_insert_iff]
  rw [Subtype.ext_iff]

omit [Fintype I] in
 theorem remainingConditions_cons_other (e : Edge cs u b) (p : List (Edge cs u b))
    (x : Interval cs u b) (hne : source cs u b e ≠ x) :
    remainingConditions cs u b (e::p) x = remainingConditions cs u b p x := by
  ext f
  have hf : f.val ≠ e := by
    intro he
    exact hne (he ▸ f.property)
  simp [remainingConditions,hf]

 theorem scheduleState_step (e : Edge cs u b) (p : List (Edge cs u b))
    (hinc : B.sheaf.lowerImage e (remainingConditions cs u b p ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b p ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    scheduleState cs u b basis hub B t p ≤
      step (source cs u b) (target cs u b) (t⁻¹-t) e
        (scheduleState cs u b basis hub B t (e::p)) := by
  classical
  intro x
  by_cases hx : (graph cs u b).source e = x
  · subst x
    have h := normalized_edge_increment_le cs u b basis hub B e
      (remainingConditions cs u b p ((graph cs u b).source e))
      (remainingConditions cs u b p ((graph cs u b).target e)) hinc ht ht1
    have hne : source cs u b e ≠ target cs u b e :=
      ne_of_lt ((graph cs u b).increasing e)
    change normalizedKernel cs u b basis hub B t (source cs u b e)
        (remainingConditions cs u b p (source cs u b e)) ≤
      normalizedKernel cs u b basis hub B t (source cs u b e)
        (remainingConditions cs u b (e::p) (source cs u b e)) +
      if source cs u b e = source cs u b e then
        (t⁻¹-t) * normalizedKernel cs u b basis hub B t (target cs u b e)
          (remainingConditions cs u b (e::p) (target cs u b e)) else 0
    rw [ite_eq_left rfl,remainingConditions_cons_source,
      remainingConditions_cons_other cs u b e p (target cs u b e) hne]
    exact h
  · simp only [scheduleState,step]
    have hx' : source cs u b e ≠ x := hx
    rw [ite_eq_right hx',add_zero,remainingConditions_cons_other cs u b e p x hx]


 theorem edgeImages_eq_of_scheduleState_eq (p : List (Edge cs u b))
    (hinc : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hend : scheduleState cs u b basis hub B t [] =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub B t p) p.reverse) :
    ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) =
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e) := by
  classical
  have heq := remaining_steps_eq (source cs u b) (target cs u b) (t⁻¹-t)
    (Comparison.transferCoefficient_pos ht ht1).le
    (scheduleState cs u b basis hub B t) p
    (fun e _ => ne_of_lt ((graph cs u b).increasing e))
    (fun e q hq => scheduleState_step cs u b basis hub B e q (hinc e q hq) ht ht1) hend
  intro e q hq
  apply (normalized_edge_increment_eq_iff cs u b basis hub B e
    (remainingConditions cs u b q ((graph cs u b).source e))
    (remainingConditions cs u b q ((graph cs u b).target e)) (hinc e q hq) ht ht1).mp
  have h := congrFun (heq e q hq) ((graph cs u b).source e)
  have hne : source cs u b e ≠ target cs u b e :=
    ne_of_lt ((graph cs u b).increasing e)
  change normalizedKernel cs u b basis hub B t (source cs u b e)
      (remainingConditions cs u b q (source cs u b e)) =
    normalizedKernel cs u b basis hub B t (source cs u b e)
      (remainingConditions cs u b (e::q) (source cs u b e)) +
    (if source cs u b e = source cs u b e then
      (t⁻¹-t) * normalizedKernel cs u b basis hub B t (target cs u b e)
        (remainingConditions cs u b (e::q) (target cs u b e)) else 0) at h
  rw [ite_eq_left rfl,remainingConditions_cons_source,
    remainingConditions_cons_other cs u b e q (target cs u b e) hne] at h
  exact h

end
end KLInvariance.BruhatGraph

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

local instance instDecidable_solutions_8_r36b5c4_1 (p : Prop) : Decidable p := Classical.propDecidable p
omit [Fintype I] in
 theorem transportedScore_eq (e : Edge cs u b) : transportedScore φ e =
    toLex (transportedSlope φ e,transportedSlope φ e) := by
  unfold transportedScore lexEdgeScore lexRootScore transportedSlope
  rw [geometricFunctional_normalizedRoot]

omit [Fintype I] in
 theorem chronologicalSchedule_pairwise : (chronologicalSchedule φ).Pairwise
    (fun e f => transportedSlope φ e ≤ transportedSlope φ f) := by
  rw [chronologicalSchedule,List.pairwise_reverse]
  apply (transportedSchedule_pairwise φ).imp
  intro e f h
  have hh := Prod.Lex.monotone_fst _ _ h
  rw [transportedScore_eq,transportedScore_eq] at hh
  exact hh

omit [Fintype I] in
 theorem chronologicalSchedule_nodup : (chronologicalSchedule φ).Nodup :=
  List.nodup_reverse.mpr (transportedSchedule_nodup φ)

omit [Fintype I] in
 theorem chronologicalSchedule_full (e : Edge cs u b) : e ∈ chronologicalSchedule φ :=
  List.mem_reverse.mpr (transportedSchedule_full φ e)

omit [Fintype I] in
 theorem transportedSlope_source_unique (e f : Edge cs u b)
    (hs : source cs u b e=source cs u b f)
    (h : transportedSlope φ e=transportedSlope φ f) : e=f := by
  have hr := congrArg rootRef (geometricSlope_injective h)
  rw [AdaptedDyer.rootRef_rootLabel,AdaptedDyer.rootRef_rootLabel] at hr
  change (φ (target cs u b e)).val * (φ (source cs u b e)).val⁻¹ =
    (φ (target cs u b f)).val * (φ (source cs u b f)).val⁻¹ at hr
  rw [hs] at hr
  apply Subtype.ext
  exact Prod.ext hs (φ.injective (Subtype.ext (mul_right_cancel hr)))

omit [Fintype I] in
 theorem transportedSlope_path_ne (e f : Edge cs u b)
    (hs : target cs u b e=source cs u b f) :
    transportedSlope φ e ≠ transportedSlope φ f := by
  intro h
  exact AdaptedDyer.rootLabel_ne_of_join cs' (transportedEdge φ e) (transportedEdge φ f)
    (congrArg (fun x => (φ x).val) hs) (geometricSlope_injective h)

omit [Fintype I] in
 theorem suffix_source_iff {e f : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) (hf : source cs u b f=source cs u b e) :
    f ∈ q ↔ transportedSlope φ e < transportedSlope φ f :=
  mem_suffix_iff_score_lt_injective (transportedSlope φ) (chronologicalSchedule_pairwise φ)
    (chronologicalSchedule_nodup φ) hq (chronologicalSchedule_full φ f)
    (transportedSlope_source_unique φ e f hf.symm)

omit [Fintype I] in
 theorem suffix_target_iff {e f : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) (hf : source cs u b f=target cs u b e) :
    f ∈ q ↔ transportedSlope φ e < transportedSlope φ f :=
  mem_suffix_iff_score_lt (transportedSlope φ) (chronologicalSchedule_pairwise φ)
    hq (chronologicalSchedule_full φ f) (transportedSlope_path_ne φ e f hf.symm)

omit [Fintype I] in
 theorem ambientLater_upperInclusion (e f : Edge cs u b) :
    (upperInclusion cs u b).edge f ∈ ambientLater φ
      (AdaptedDyer.rootLabel cs' (transportedEdge φ e)) ↔
    transportedSlope φ e < transportedSlope φ f := by
  have hs : BruhatStep cs' (φ (source cs u b f)).val (φ (target cs u b f)).val :=
    (transportedEdge φ f).property
  have hiff : ambientAfterIndicator (φ (source cs u b f)).val
      (AdaptedDyer.rootLabel cs' (transportedEdge φ e))
      (φ (target cs u b f)).val = 1 ↔ transportedSlope φ e < transportedSlope φ f := by
    simp only [ambientAfterIndicator,dite_eq_left hs]
    change (if transportedSlope φ e < transportedSlope φ f then 1 else 0)=1 ↔ _
    split_ifs <;> simp_all
  constructor
  · rintro ⟨_,h⟩
    exact hiff.mp h
  · intro h
    exact ⟨(source cs u b f).property.1,hiff.mpr h⟩

omit [Fintype I] in
 theorem remainingConditions_source_ambient {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) :
    remainingConditions cs u b q (source cs u b e) =
      {f | (upperInclusion cs u b).edge f.val ∈ ambientLater φ
        (AdaptedDyer.rootLabel cs' (transportedEdge φ e))} := by
  ext f
  exact (suffix_source_iff φ hq f.property).trans (ambientLater_upperInclusion φ e f.val).symm

omit [Fintype I] in
 theorem remainingConditions_target_ambient {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) :
    remainingConditions cs u b q (target cs u b e) =
      {f | (upperInclusion cs u b).edge f.val ∈ ambientLater φ
        (AdaptedDyer.rootLabel cs' (transportedEdge φ e))} := by
  ext f
  exact (suffix_target_iff φ hq f.property).trans (ambientLater_upperInclusion φ e f.val).symm

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/

section

namespace KLInvariance.MomentGraph.Sheaf.Iso
universe ur uv ue uz uz'
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
  {B : Sheaf.{ur,uv,ue,uz} (R := R) G} {C : Sheaf.{ur,uv,ue,uz'} (R := R) G}
  (j : Iso B C)

include j in
 theorem scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (h : B.ScaledImages e F H r) : C.ScaledImages e F H r := by
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' : (j.vertex (G.source e)).symm v ∈ B.upwardKernel (G.source e) F := by
      apply (j.upwardKernel_iff _ _ _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hv
    have he' : B.lower e ((j.vertex (G.source e)).symm v)=(j.edge e).symm z := by
      apply (j.edge e).injective
      rw [j.lower,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,he]
    obtain ⟨w,hw,hew⟩ := (h ((j.edge e).symm z)).mp ⟨_,hv',he'⟩
    refine ⟨j.vertex (G.target e) w,(j.upwardKernel_iff _ _ _).mpr hw,?_⟩
    rw [← j.upper,← map_smul,hew,LinearEquiv.apply_symm_apply]
  · rintro ⟨w,hw,he⟩
    have hw' : (j.vertex (G.target e)).symm w ∈ B.upwardKernel (G.target e) H := by
      apply (j.upwardKernel_iff _ _ _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hw
    have he' : r • B.upper e ((j.vertex (G.target e)).symm w)=(j.edge e).symm z := by
      apply (j.edge e).injective
      rw [map_smul,j.upper,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,he]
    obtain ⟨v,hv,hev⟩ := (h ((j.edge e).symm z)).mpr ⟨_,hw',he'⟩
    refine ⟨j.vertex (G.source e) v,(j.upwardKernel_iff _ _ _).mpr hv,?_⟩
    rw [← j.lower,hev,LinearEquiv.apply_symm_apply]

end KLInvariance.MomentGraph.Sheaf.Iso

end


section

namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

/-- A quotient-product equality gives the actual two embedded model images.
The common quotient is the edge module's coefficient ring. -/
 theorem structure_scaledImages (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (h : Associated
      (algebraMap R (R ⧸ Ideal.span {α e}) (kernelProduct G α c (G.source e) F))
      (algebraMap R (R ⧸ Ideal.span {α e}) (r*kernelProduct G α c (G.target e) H))) :
    (structureSheaf G α c).ScaledImages e F H r := by
  rw [scaledImages_iff,structure_lower_image (G := G) α c e F hF,
    structure_upper_image (G := G) α c e H hH,← mul_smul]
  let S := R ⧸ Ideal.span {α e}
  let : Module S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (Module S (PLift (G.target e ≤ c) → S))
  let : IsScalarTower R S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (IsScalarTower R S (PLift (G.target e ≤ c) → S))
  exact LocalProducts.smul_top_eq_of_map_associated (S := S) h

 theorem structure_scaledImages_of_count (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) (p : R ⧸ Ideal.span {α e}) (k : ℕ)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (ha : ∀ i ∈ supportedOutgoing G c (G.source e) F,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hb : ∀ i ∈ supportedOutgoing G c (G.target e) H,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hr : Associated (algebraMap R (R ⧸ Ideal.span {α e}) r) (p^k))
    (hc : (supportedOutgoing G c (G.source e) F).card=
      (supportedOutgoing G c (G.target e) H).card+k) :
    (structureSheaf G α c).ScaledImages e F H r := by
  apply structure_scaledImages G α c e F H r hF hH
  simpa only [kernelProduct,map_prod,map_mul] using
    LocalProducts.associated_prod_scale _ _ _ _ p _ k ha hb hr hc

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledLower_root_ne (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.1)
    (hf : f ∈ B.scheduledLower hmin φ e hx) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  intro he
  have hroot : BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin f.val) =
      BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) := by
    rwa [B.cosetRoot_eq a₀ b hmin f.val,B.cosetRoot_eq a₀ b hmin e]
  have hh : f.val=e := B.cosetEdgeAmbient_injective a₀ b hmin
    (eq_of_label_source_eq cs 1 b (root_injective_on_labels cs 1 b hroot)
      (congrArg (B.cosetAmbient a₀ b) f.property))
  have hff : f=(⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) := Subtype.ext hh
  exact B.scheduledLower_self hmin φ e hx (hff ▸ hf)

 theorem outgoingUpper_root_ne (e : B.CosetEdge a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.2) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=e.val.2 at hs
  subst s
  exact (B.edgeRoot_ne_of_path e.property hst).symm

 theorem coset_structure_scaledImages [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  by_cases hyc : e.val.2 ≤ c
  · let α := B.edgeRoot e.property
    obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
      by_cases h : α=B.left
      · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
      · exact ⟨B.left,h,B.left_mem⟩
    have hplane : rootPlane α β=P :=
      (rootPlane_eq_of_mem B.left B.right α β B.distinct
        (B.plane_eq.ge (B.edgeRoot_plane e.property)) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq
    apply structure_scaledImages_of_count (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c
      e _ _ _ (B.reducedCosetRoot basis a₀ b hmin e β)
      ((planeWeight ((e.val.1.val:W)*a₀) α P).toNat)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.1 _)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.2 _)
    · intro f hf
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.scheduledLower_root_ne hmin φ e hx f (Finset.mem_filter.mp hf).2.1)
    · intro f _
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.outgoingUpper_root_ne e f)
    · exact B.cosetFactor_reduction_associated basis a₀ b hmin e β hαβ hplane
    · exact B.supported_count_difference hmin φ e hx c hyc
  · let := structureSheaf_edge_subsingleton (B.cosetGraph a₀ b)
        (B.cosetLabel basis a₀ b hmin) c e hyc
    intro z
    constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localized_boundary_decomposition :
    ∃ C : Sheaf.{max us v,v,v,max us v} (R := PlaneRing basis P) (B.cosetGraph a₀ b),
      ModelSum (B.cosetModels basis a₀ b hmin).sheaf Set.univ C ∧
      Nonempty (Iso (B.localizedCoset basis a₀ b hmin
        (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget) C) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  apply exists_modelSumIso (B.cosetModels basis a₀ b hmin)
    (B.localizedCoset basis a₀ b hmin D.sheaf.forget)
  · intro x
    let : Module.Free (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      D.free (B.cosetAmbient a₀ b x)
    exact D.sheaf.forget.baseChange_vertex_free (PlaneRing basis P) _
  · intro x
    let : Module.Finite (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      (D.sheaf.vertex (B.cosetAmbient a₀ b x)).finite
    exact D.sheaf.forget.baseChange_vertex_finite (PlaneRing basis P) _
  · exact B.localizedCoset_quotient basis a₀ b hmin D.sheaf.forget D.quotient
  · exact B.localizedCoset_flabby basis a₀ b hmin D.sheaf.forget D.quotient D.flabby.flabby
  · exact B.localizedCoset_generated basis a₀ b hmin D.sheaf.forget D.generated

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem localized_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (B.localizedCoset basis a₀ b hmin
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  let : Finite (B.CosetEdge a₀ b) := Finite.of_injective
    (fun e : B.CosetEdge a₀ b => e.val) Subtype.val_injective
  let := Fintype.ofFinite (B.CosetEdge a₀ b)
  obtain ⟨C,hC,⟨j⟩⟩ := B.localized_boundary_decomposition basis a₀ b hmin
  apply j.symm.scaledImages
  apply hC.scaledImages
  intro c _
  exact B.coset_structure_scaledImages basis hmin φ e hx c

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Flat scalar extension of actual embedded kernel and image modules. -/
namespace KLInvariance.FlatSubmodule
open TensorProduct
universe ur us um un
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]

 theorem baseChange_ker [Module.Flat R S] (f : M →ₗ[R] N) :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  ext z
  exact (Module.Flat.lTensor_exact S f.exact_subtype_ker_map z).symm

 theorem baseChange_map (p : Submodule R M) (f : M →ₗ[R] N) :
    (p.map f).baseChange S = (p.baseChange S).map (f.baseChange S) := by
  apply le_antisymm
  · rintro z ⟨k,rfl⟩
    induction k using OAI.tensorInductionOn with
    | tmul s x =>
      obtain ⟨m,hm,hx⟩ := x.property
      refine ⟨s ⊗ₜ m,Submodule.tmul_mem_baseChange_of_mem s hm,?_⟩
      change s ⊗ₜ[R] f m = s ⊗ₜ[R] (x : N)
      rw [hx]
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rintro z ⟨w,⟨k,hk⟩,rfl⟩
    subst w
    induction k using OAI.tensorInductionOn with
    | tmul s x =>
      exact Submodule.tmul_mem_baseChange_of_mem s (show f x ∈ p.map f from ⟨x,x.property,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

end KLInvariance.FlatSubmodule

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 theorem ker_kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    LinearMap.ker (B.kernelConstraint x F) = B.upwardKernel x F := by
  ext v
  constructor
  · intro h e he
    exact congrFun (LinearMap.mem_ker.mp h) ⟨e,he⟩
  · intro h
    exact LinearMap.mem_ker.mpr (funext fun e => h e.val e.property)

 theorem kernelConstraint_tensor (x : V) (F : Set (Outgoing (G := G) x))
    (z : S ⊗[R] B.vertex x) :
    (B.baseChange S).kernelConstraint x F z =
      TensorProduct.piRightHom R S S (fun e : F => B.edge e.val.val)
        ((B.kernelConstraint x F).baseChange S z) := by
  let k : (S ⊗[R] B.vertex x) →ₗ[S] (∀ e : F, S ⊗[R] B.edge e.val.val) :=
    (B.baseChange S).kernelConstraint x F
  change k z = _
  induction z using OAI.tensorInductionOn with
  | tmul s v =>
    funext e
    rcases e with ⟨⟨e,he⟩,heF⟩
    subst x
    rfl
  | add z t hz ht =>
    simp only [map_add,hz,ht]

 theorem baseChange_upwardKernel [Finite E] [Module.Flat R S]
    (x : V) (F : Set (Outgoing (G := G) x)) :
    (B.upwardKernel x F).baseChange S = (B.baseChange S).upwardKernel x F := by
  classical
  let := Fintype.ofFinite E
  rw [← B.ker_kernelConstraint x F,FlatSubmodule.baseChange_ker,
    ← (B.baseChange S).ker_kernelConstraint x F]
  ext z
  change (B.kernelConstraint x F).baseChange S z = 0 ↔
    (B.baseChange S).kernelConstraint x F z = 0
  rw [B.kernelConstraint_tensor S]
  exact ((TensorProduct.piRight R S S (fun e : F => B.edge e.val.val)).map_eq_zero_iff).symm

 theorem baseChange_lowerImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.source e))) :
    ((B.upwardKernel (G.source e) F).map (B.lower e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.source e) F).map ((B.baseChange S).lower e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

 theorem baseChange_upperImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.target e))) :
    ((B.upwardKernel (G.target e) F).map (B.upper e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.target e) F).map ((B.baseChange S).upper e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {a₀ b : W}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localizedCoset_kernel
    (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis))
    (x : B.CosetVertex a₀ b) (T : Set (Edge cs 1 b)) :
    (B.localizedCoset basis a₀ b hmin C).upwardKernel x
      {e | B.cosetEdgeAmbient a₀ b hmin e.val ∈ T} =
    (C.baseChange (PlaneRing basis P)).upwardKernel (B.cosetAmbient a₀ b x) {e | e.val ∈ T} := by
  apply (C.baseChange (PlaneRing basis P)).pullback_kernel (B.cosetGraphMap a₀ b hmin) x T
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · intro e he hx
    exact B.coset_lift_live a₀ b hmin e he x hx

end

variable {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem ambient_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (B.mappedCosetRoot hmin φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin e)
      {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  have h := B.localized_boundary_scaledImages basis hmin φ e hx
  dsimp only
  intro z
  have hh := h z
  change (∃ v ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.1
      (B.scheduledOutgoing hmin φ _ e.val.1 hx), _) ↔
    ∃ w ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.2
      (B.scheduledOutgoing hmin φ _ e.val.2 (B.cosetEdge_target_upper hmin e hx)), _ at hh
  rw [B.scheduledOutgoing_eq hmin φ,B.scheduledOutgoing_eq hmin φ,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient] at hh
  exact hh

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The local embedded image identity at every actual root-plane prime.
The edge is arbitrary in [1,b], with source in the comparison interval. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_plane_scaledImages (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    (β : PositiveRoot M cs) (hβ : root cs 1 b e ≠ β) :
    let P := rootPlane (root cs 1 b e) β
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages e {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let P := rootPlane (root cs 1 b e) β
  let B := (nonempty_planeBasis (root cs 1 b e) β hβ).some
  obtain ⟨a₀,hmin,d,hd⟩ := B.exists_coset_edge e (Submodule.subset_span (by simp))
  have hdx : BruhatLE cs u ((d.val.1.val:W)*a₀) := by
    change BruhatLE cs u (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
    rwa [hd]
  have h := B.ambient_boundary_scaledImages hmin basis φ d hdx
  dsimp only at h ⊢
  rw [B.mappedCosetRoot_eq hmin φ d hdx,
    show B.edgeRoot d.property=root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d) from
      (B.cosetRoot_eq a₀ b hmin d).symm] at h
  change ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
    (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin d)
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (edgeFactorLift cs basis (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
        (root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)))) at h
  have h' := h
  simp only [hd] at h'
  exact Eq.mp (congrArg (fun z : Edge cs 1 b =>
    ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
      (PlaneRing basis P)).ScaledImages z
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e)))) hd) h'

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance edgeRing_isDomain (a : PositiveRoot M cs) : IsDomain (EdgeRing cs basis a) := by
   let : (Ideal.span {polynomialRoot cs basis a}).IsPrime :=
     Ideal.isPrime_span_singleton_of_prime (polynomialRoot_prime cs basis a)
   infer_instance

 theorem reducedPolynomialRoot_prime (a β : PositiveRoot M cs) (hne : a≠β) :
    Prime (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)) := by
  apply (MulEquiv.prime_iff (edgeRingEquiv cs basis a)).mp
  rw [edgeRingEquiv_root]
  exact reducedRoot_prime _ _ (embed_not_rootLine a β hne.symm)

 theorem planePrime_span (a β : PositiveRoot M cs) :
    planePrime basis (rootPlane a β) =
      Ideal.span {polynomialRoot cs basis a,polynomialRoot cs basis β} := by
  simp only [planePrime,rootPlane,Submodule.map_span,Set.image_insert_eq,
    Set.image_singleton,SymmetricPlaneIdeal.ideal_span_eq,Ideal.map_span,
    polynomialRoot,embedLinear]
  rfl

end
end KLInvariance.BruhatGraph

end


section

/-! The scalar quotient of an actual finite free presentation is free over
its quotient coefficient ring. There is no quotient-freeness hypothesis. -/
namespace KLInvariance.ScalarQuotient
open Module
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {ι : Type ui} [Fintype ι]
noncomputable section

 theorem coordinateReduction_surjective (b : Basis ι R M) (a : R) :
    Function.Surjective (coordinateReduction b a) := by
  intro v
  choose w hw using fun i => Ideal.Quotient.mk_surjective (v i)
  exact ⟨b.equivFun.symm w,funext fun i => by
    change Ideal.Quotient.mk (Ideal.span {a}) (b.equivFun (b.equivFun.symm w) i)=v i
    simpa only [LinearEquiv.apply_symm_apply] using hw i⟩

 theorem coordinateReduction_kernel (b : Basis ι R M) (a : R) (v : M) :
    coordinateReduction b a v=0 ↔ ∃ w, v=a • w := by
  have h : (∃ w, v=a • w) ↔ ∀ i, a ∣ b.equivFun v i :=
    (exists_congr fun _ => eq_comm).trans (FiniteFreeScalar.exists_smul_iff b a v)
  rw [h]
  simp only [coordinateReduction,LinearMap.pi_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,LinearEquiv.coe_coe,funext_iff,Pi.zero_apply]
  exact forall_congr' fun i => (Ideal.Quotient.eq_zero_iff_mem).trans Ideal.mem_span_singleton

 theorem free_of_scalar_presentation (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (b : Basis ι R M) (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w) :
    Module.Free (R ⧸ Ideal.span {a}) N := by
  obtain ⟨j,_⟩ := QuotientEdge.exists_scalar_iso q (coordinateReduction b a) a
    hq (coordinateReduction_surjective b a) hk (coordinateReduction_kernel b a)
    (LinearEquiv.refl R M)
  let k : N ≃ₗ[R ⧸ Ideal.span {a}] (ι → R ⧸ Ideal.span {a}) :=
    { j.toAddEquiv with
      map_smul' := by
        intro c v
        obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
        change j ((algebraMap R (R ⧸ Ideal.span {a}) r) • v) =
          (algebraMap R (R ⧸ Ideal.span {a}) r) • j v
        simpa only [algebraMap_smul] using j.map_smul r v }
  exact Module.Free.of_equiv k.symm

 theorem saturated_image_free (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (q : M →ₗ[R] N) (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w)
    (L : Submodule R M) [Module.Free R L] [Module.Finite R L]
    (hsat : ∀ v, a • v ∈ L → v ∈ L) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (L.map q)) := by
  let f : L →ₗ[R] submodule a (L.map q) :=
    (q.comp L.subtype).codRestrict ((submodule a (L.map q)).restrictScalars R)
      (fun v => ⟨v.val,v.property,rfl⟩)
  apply free_of_scalar_presentation a (Module.Free.chooseBasis R L) f
  · rintro ⟨v,hv⟩
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨⟨w,hw⟩,rfl⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨w,hw⟩ := (hk v.val).mp (congrArg Subtype.val hv)
      exact ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      exact Subtype.ext ((hk _).mpr ⟨w.val,rfl⟩)

end
end KLInvariance.ScalarQuotient

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem edgeModule_free (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ := B.free (target cs u b e)
   exact ScalarQuotient.free_of_scalar_presentation _
     (Module.Free.chooseBasis (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)))
     (B.sheaf.upper e).map (B.quotient e).1 (B.quotient e).2

 theorem upperImage_free (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) (target cs u b e)))
    [Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F)] :
    let _ := edgeModule cs u b basis hub B e
    let _ := edgeModule_tower cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e))
      (ScalarQuotient.submodule (polynomialRoot cs basis (root cs u b e))
        ((B.sheaf.upwardSubmodule (target cs u b e) F).map (B.sheaf.upper e).map)) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)) :=
     (B.sheaf.vertex (target cs u b e)).finite
   let hfinite : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F) :=
     Module.Finite.of_injective (B.sheaf.upwardSubmodule (target cs u b e) F).subtype Subtype.val_injective
   dsimp only
   let hfree := (inferInstance : Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F))
   exact @ScalarQuotient.saturated_image_free (MvPolynomial σ ℝ) _
     (B.sheaf.vertex (target cs u b e)) _ _ (B.sheaf.edge e) _ _
     (polynomialRoot cs basis (root cs u b e)) _ _
     (B.sheaf.upper e).map (B.quotient e).2 (B.sheaf.upwardSubmodule (target cs u b e) F)
     hfree hfinite (by

     exact B.sheaf.upwardSubmodule_saturated (target cs u b e) F _
            (fun f _ => incoming_label_regular_outgoing cs u b basis hub B e f.val f.property))

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reducedRoot_dvd_iff_mem_plane (a β : PositiveRoot M cs) (z : MvPolynomial σ ℝ) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) (polynomialRoot cs basis β) ∣
      Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) z ↔
    z ∈ planePrime basis (rootPlane a β) := by
  rw [← Ideal.mem_span_singleton]
  change z ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)}) ↔ _
  have hi : Ideal.map (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
      (Ideal.span {polynomialRoot cs basis β}) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
        (polynomialRoot cs basis β)} := by rw [Ideal.map_span,Set.image_singleton]
  rw [← hi,Ideal.comap_map_quotientMk,← Ideal.span_union,Set.singleton_union,planePrime_span]

 theorem reducedFactor_ne_zero (x : W) (a : PositiveRoot M cs) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (edgeFactorLift cs basis x a) ≠ 0 := by
  simpa only [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton] using
    edgeFactorLift_not_dvd cs basis x a

 theorem prime_dvd_reducedFactor (x : W) (a : PositiveRoot M cs)
    (p : EdgeRing cs basis a) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _ (edgeFactorLift cs basis x a)) :
    ∃ β : PositiveRoot M cs, a ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  simp only [edgeFactorLift,map_prod,map_pow] at hd
  obtain ⟨P,_,hP⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨planeRoot x a P,(planeRoot_ne x a P).symm,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis a _ (planeRoot_ne x a P).symm).irreducible
      (hp.dvd_of_dvd_pow hP)⟩

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section
open scoped Classical

 theorem outgoingLabelProduct_dvd (α : E → R) (x : V) (F : Set (Outgoing (G := G) x))
    (f : Outgoing (G := G) x) (hf : f ∈ F) : α f.val ∣ outgoingLabelProduct α x F := by
   exact Finset.dvd_prod_of_mem _ (F.toFinite.mem_toFinset.mpr hf)

 theorem outgoingLabelProduct_smul_mem (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    outgoingLabelProduct α x F • v ∈ B.upwardKernel x F := by
   intro f hf
   obtain ⟨r,hr⟩ := outgoingLabelProduct_dvd α x F f hf
   rw [map_smul,hr,mul_comm,mul_smul]
   have h := hα f.val (B.stalkMap x v f)
   change r • (α f.val • B.stalkMap x v f) = 0
   rw [h,smul_zero]

 theorem outgoingLabelProduct_smul_upperImage (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (e : E) (hq : Function.Surjective (B.upper e))
    (F : Set (Outgoing (G := G) (G.target e))) (v : B.edge e) :
    outgoingLabelProduct α (G.target e) F • v ∈
      (B.upwardKernel (G.target e) F).map (B.upper e) := by
   obtain ⟨w,rfl⟩ := hq v
   exact ⟨_,B.outgoingLabelProduct_smul_mem α hα _ F w,(B.upper e).map_smul _ w⟩

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem incoming_root_ne_outgoing (e f : Edge cs u b)
    (h : source cs u b f=target cs u b e) : root cs u b e ≠ root cs u b f := by
  intro hr
  exact source_ne_target_of_label_eq cs u b (root_injective_on_labels cs u b hr.symm) h

 theorem reducedKernelProduct_ne_zero (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e))) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis (root cs u b e)})
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F) ≠ 0 := by
  classical
  rw [outgoingLabelProduct,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro f _
  exact (reducedPolynomialRoot_prime cs basis _ _
    (incoming_root_ne_outgoing cs u b e f.val f.property)).ne_zero

 theorem prime_dvd_reducedKernelProduct (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e)))
    (p : EdgeRing cs basis (root cs u b e)) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F)) :
    ∃ β : PositiveRoot M cs, root cs u b e ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  rw [outgoingLabelProduct,map_prod] at hd
  obtain ⟨f,_,hf⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨root cs u b f.val,incoming_root_ne_outgoing cs u b e f.val f.property,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis _ _
        (incoming_root_ne_outgoing cs u b e f.val f.property)).irreducible hf⟩

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.ScalarQuotient
universe ur un
variable {R : Type ur} [CommRing R]
  {N : Type un} [AddCommGroup N] [Module R N]
noncomputable section

 theorem scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) :
    submodule a (S.map (LinearMap.lsmul R N z)) =
      (submodule a S).map
        (LinearMap.lsmul (R ⧸ Ideal.span {a}) N (Ideal.Quotient.mk _ z)) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact algebraMap_smul _ _ w⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact (algebraMap_smul _ _ w).symm⟩

 theorem free_scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) [Module.Free (R ⧸ Ideal.span {a}) (submodule a S)]
    (hz : Function.Injective (fun v : N => z • v)) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (S.map (LinearMap.lsmul R N z))) := by
  rw [scalarImage]
  apply Module.Free.of_equiv (Submodule.equivMapOfInjective _ ?_ (submodule a S))
  intro v w h
  apply hz
  change (algebraMap R (R ⧸ Ideal.span {a}) z) • v =
    (algebraMap R (R ⧸ Ideal.span {a}) z) • w at h
  simpa only [algebraMap_smul] using h

end
end KLInvariance.ScalarQuotient

end


section

namespace KLInvariance.TensorLocalMembership
open TensorProduct
universe ur us um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem baseChange_eq_localized (L : Submodule R M) :
    L.baseChange S = L.localized' S P (TensorProduct.mk R S M 1) := by
  rw [Submodule.baseChange_eq_span,Submodule.localized'_eq_span]
  rfl

 theorem denominator (L : Submodule R M) (x : M)
    (hx : 1 ⊗ₜ[R] x ∈ L.baseChange S) :
    ∃ a : P, (a:R) • x ∈ L := by
  rw [baseChange_eq_localized S P L] at hx
  obtain ⟨m,hm,s,hs⟩ := hx
  have he := (IsLocalizedModule.mk'_eq_iff).mp hs
  change (TensorProduct.mk R S M 1) m = (s:R) • (TensorProduct.mk R S M 1) x at he
  rw [← map_smul] at he
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_iff_exists P (TensorProduct.mk R S M 1)).mp he
  refine ⟨t*s,?_⟩
  have hh := L.smul_mem (t:R) hm
  change (t:R) • m ∈ L at hh
  change (t:R) • m = (t:R) • ((s:R) • x) at ht
  simpa only [Submonoid.coe_mul,mul_smul,← ht] using hh

end
end KLInvariance.TensorLocalMembership

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem scaledImages_denominator
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (a : R)
    (h : (B.baseChange S).ScaledImages e F H (algebraMap R S a))
    (x : B.edge e) (hx : x ∈ (B.upwardKernel (G.source e) F).map (B.lower e)) :
    ∃ s : P, (s:R) • x ∈ ((B.upwardKernel (G.target e) H).map (B.upper e)).map
      (LinearMap.lsmul R (B.edge e) a) := by
  let _ : Module.Flat R S := IsLocalization.flat S P
  apply TensorLocalMembership.denominator S P _ x
  rw [FlatSubmodule.baseChange_map,B.baseChange_upperImage S]
  have hx' : 1 ⊗ₜ[R] x ∈ ((B.baseChange S).upwardKernel (G.source e) F).map
      ((B.baseChange S).lower e) := by
    rw [← B.baseChange_lowerImage S]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  obtain ⟨v,hv,he⟩ := hx'
  obtain ⟨w,hw,hwx⟩ := (h (1 ⊗ₜ[R] x)).mp ⟨v,hv,he⟩
  refine ⟨(B.baseChange S).upper e w,⟨w,hw,rfl⟩,?_⟩
  change (LinearMap.lsmul R (B.edge e) a).baseChange S ((B.baseChange S).upper e w) = _
  have hg : (LinearMap.lsmul R (B.edge e) a).baseChange S =
      LinearMap.lsmul S (S ⊗[R] B.edge e) (algebraMap R S a) := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro r v
    change (LinearMap.lsmul R (B.edge e) a).baseChange S (r ⊗ₜ[R] v) =
      (algebraMap R S a) • (r ⊗ₜ[R] v)
    simp only [LinearMap.baseChange_tmul,LinearMap.lsmul_apply,
      algebraMap_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul']
  rw [hg]
  exact hwx

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace
universe u v us un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem mem_of_plane_denominators (a : PositiveRoot M cs)
    {N : Type un} [AddCommGroup N] [Module (MvPolynomial σ ℝ) N]
    [Module (EdgeRing cs basis a) N] [IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) N]
    [Module.IsTorsionFree (EdgeRing cs basis a) N]
    (S : Submodule (MvPolynomial σ ℝ) N)
    [Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S)]
    (z : N) (c : MvPolynomial σ ℝ)
    (hc : Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c ≠ 0)
    (hcz : c • z ∈ S)
    (hprime : ∀ p : EdgeRing cs basis a, Prime p → p ∣ Ideal.Quotient.mk _ c →
      ∃ β : PositiveRoot M cs, a≠β ∧ Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)))
    (hlocal : ∀ β : PositiveRoot M cs, a≠β →
      ∃ s : MvPolynomial σ ℝ, s ∉ planePrime basis (rootPlane a β) ∧ s • z ∈ S) :
    z ∈ S := by
  apply EdgeLattice.mem_of_prime_local_membership
    (ScalarQuotient.submodule (polynomialRoot cs basis a) S) z
  · refine ⟨Ideal.Quotient.mk _ c,hc,?_⟩
    change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
    simpa only [algebraMap_smul] using hcz
  · intro p hp
    by_cases hpc : p ∣ Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c
    · obtain ⟨β,hβ,hpβ⟩ := hprime p hp hpc
      obtain ⟨s,hs,hsz⟩ := hlocal β hβ
      refine ⟨Ideal.Quotient.mk _ s,?_,?_⟩
      · rw [hpβ.dvd_iff_dvd_left,reducedRoot_dvd_iff_mem_plane]
        exact hs
      · change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) s) • z ∈ S
        simpa only [algebraMap_smul] using hsz
    · refine ⟨Ideal.Quotient.mk _ c,hpc,?_⟩
      change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
      simpa only [algebraMap_smul] using hcz

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_edge_image_le (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    [Module.Free (MvPolynomial σ ℝ)
      ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.upwardSubmodule
        (target cs 1 b e) {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)})] :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.upwardKernel (source cs 1 b e) {f | f.val ∈ T}).map (D.lower e) ≤
      ((D.upwardKernel (target cs 1 b e) {f | f.val ∈ T}).map (D.upper e)).map
        (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e)
          (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let D := B.sheaf.forget
  let F : Set (Outgoing (G := graph cs 1 b) (source cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let G : Set (Outgoing (G := graph cs 1 b) (target cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let a := root cs 1 b e
  let f := edgeFactorLift cs basis (source cs 1 b e).val a
  let J := (D.upwardKernel (target cs 1 b e) G).map (D.upper e)
  let S := J.map (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e) f)
  let pG := outgoingLabelProduct (polynomialLabel cs 1 b basis) (target cs 1 b e) G
  let _ : Module (EdgeRing cs basis a) (D.edge e) :=
    edgeModule cs 1 b basis (one_bruhat cs b) B e
  let _ : IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_tower cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_free cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a)
      (ScalarQuotient.submodule (polynomialRoot cs basis a) J) :=
    upperImage_free cs 1 b basis (one_bruhat cs b) B e G
  let _ : Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S) :=
    ScalarQuotient.free_scalarImage (polynomialRoot cs basis a) f J
      (edgeFactorLift_regular cs basis 1 b (one_bruhat cs b) B e)
  change (D.upwardKernel (source cs 1 b e) F).map (D.lower e) ≤ S
  intro z hz
  apply mem_of_plane_denominators cs basis a S z (f*pG)
  · rw [map_mul]
    exact mul_ne_zero (reducedFactor_ne_zero cs basis _ a)
      (reducedKernelProduct_ne_zero cs 1 b basis e G)
  · refine ⟨pG • z,?_,?_⟩
    · exact D.outgoingLabelProduct_smul_upperImage (polynomialLabel cs 1 b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient) e (B.quotient e).1 G z
    · change f • (pG • z) = (f*pG) • z
      rw [mul_smul]
  · intro p hp hd
    rw [map_mul] at hd
    rcases hp.dvd_mul.mp hd with hf | hG
    · exact prime_dvd_reducedFactor cs basis _ a p hp hf
    · exact prime_dvd_reducedKernelProduct cs 1 b basis e G p hp hG
  · intro β hβ
    obtain ⟨s,hs⟩ := D.scaledImages_denominator (PlaneRing basis (rootPlane a β))
      (planePrime basis (rootPlane a β)).primeCompl e F G f
      (boundary_plane_scaledImages basis φ e hx β hβ) z hz
    exact ⟨s,s.property,hs⟩

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem schedule_edge_image_le {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ)
    [hF : Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
        (remainingConditions cs u b q (target cs u b e)))] :
    (intervalBoundary basis hub).sheaf.lowerImage e
        (remainingConditions cs u b q (source cs u b e)) ≤
      ((intervalBoundary basis hub).sheaf.upperImage e
        (remainingConditions cs u b q (target cs u b e))).map
        (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e) := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let a := (upperInclusion cs u b).edge e
  let r := AdaptedDyer.rootLabel cs' (transportedEdge φ e)
  have hr : mappedEdgeRoot φ a (source cs u b e).property.1 = r := rfl
  have hk (x : Interval cs u b) :=
    restrictBoundary_kernel cs u b basis hub B x (ambientLater φ r)
  have hs : (intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e)
      (remainingConditions cs u b q (source cs u b e)) =
      B.sheaf.upwardSubmodule (source cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e))
      (remainingConditions_source_ambient φ hq)).trans (hk (source cs u b e))
  have ht : (intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
      (remainingConditions cs u b q (target cs u b e)) =
      B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e))
      (remainingConditions_target_ambient φ hq)).trans (hk (target cs u b e))
  have hfree : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r}) :=
    (congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
      Module.Free (Coefficient (σ := σ)) N) ht).mp hF
  let hf : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a)
        {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ a (source cs u b e).property.1)}) := by
    rw [hr]
    exact hfree
  have h := boundary_edge_image_le basis φ a (source cs u b e).property.1
  dsimp only at h
  rw [hr] at h
  have hs' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (source cs 1 b a)) =>
    N.map (B.sheaf.lower a).map) hs
  have ht' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
    (N.map (B.sheaf.upper a).map).map
      (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e)) ht
  exact hs'.le.trans (h.trans ht'.symm.le)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem no_conditions_free (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule x (remainingConditions cs u b [] x)) := by
  have he : B.sheaf.upwardSubmodule x (remainingConditions cs u b [] x) = ⊤ := by
    ext v
    change (∀ e, e ∈ remainingConditions cs u b [] x → _) ↔ True
    simp [remainingConditions]
  rw [he]
  let := B.free x
  exact Module.Free.of_equiv (Submodule.topEquiv :
    (⊤ : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x)) ≃ₗ[Coefficient] B.sheaf.vertex x).symm

/-- Reverse traversal of the actual schedule, after embedded image equality.
Both kernels used in Schanuel have already been made free at this point. -/
 theorem schedule_kernels_free_of_images_eq (p : List (Edge cs u b))
    (heq : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) =
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e)) :
    ∀ q, q <:+ p → ∀ x : Interval cs u b,
      Module.Free (Coefficient (σ := σ))
        (B.sheaf.upwardSubmodule x (remainingConditions cs u b q x)) := by
  induction p with
  | nil =>
    intro q hq x
    have hq' : q=[] := by simpa using hq
    subst q
    exact no_conditions_free cs u b basis hub B x
  | cons e p ih =>
    have hip := ih (fun a q hq => heq a q (hq.trans (List.suffix_cons e p)))
    intro q hq x
    rcases List.suffix_cons_iff.mp hq with h | h
    · subst q
      by_cases hx : source cs u b e = x
      · subst x
        rw [remainingConditions_cons_source]
        let hS : Module.Free (Coefficient (σ := σ))
            (B.sheaf.upwardSubmodule ((graph cs u b).source e)
              (remainingConditions cs u b p (source cs u b e))) :=
          hip p (List.suffix_refl _) (source cs u b e)
        let hT : Module.Free (Coefficient (σ := σ))
            (B.sheaf.upwardSubmodule ((graph cs u b).target e)
              (remainingConditions cs u b p ((graph cs u b).target e))) :=
          hip p (List.suffix_refl _) (target cs u b e)
        exact partial_kernel_free_of_image_eq cs u b basis hub B e _ _
          (heq e p (List.suffix_refl _))
      · rw [remainingConditions_cons_other cs u b e p x hx]
        exact hip p (List.suffix_refl _) x
    · exact hip q h x

 theorem schedule_kernels_free_of_endpoint_eq (p : List (Edge cs u b))
    (hinc : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hend : scheduleState cs u b basis hub B t [] =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub B t p) p.reverse) :
    ∀ q, q <:+ p → ∀ x : Interval cs u b,
      Module.Free (Coefficient (σ := σ))
        (B.sheaf.upwardSubmodule x (remainingConditions cs u b q x)) := by
  exact schedule_kernels_free_of_images_eq cs u b basis hub B p
    (edgeImages_eq_of_scheduleState_eq cs u b basis hub B p hinc ht ht1 hend)

end
end KLInvariance.BruhatGraph

end


section

/-! Actual-character comparison: no identification with the KL basis is used.
This permits induction on R kernels rather than on stalk character recognition. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b)
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 local instance instDecidableEq_solutions_1_r36b5c4_1 (X : Type*) : DecidableEq X := Classical.decEq X
theorem actual_freeSuffixes_of_rTilde_eq_oai
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e)))) :
    FreeSuffixes basis hab φ := by
  apply schedule_kernels_free_of_endpoint_eq cs a b basis hab (intervalBoundary basis hab)
    (chronologicalSchedule φ)
    (fun e q hq => by
      let := hfree e q hq
      exact schedule_edge_image_le basis hab φ hq)
    (t := 1/2) (by norm_num) (by norm_num)
  exact actual_endpoint_of_rTilde_eq basis hab φ hr (by norm_num) (by norm_num)

end
end KLInvariance.BruhatGraph

end


end OAI
end

theorem solution.{u, u'} : type_of% @OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq_oai.{u, u'} := @OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq_oai.{u, u'}
