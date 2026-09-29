-- Prove2me | solution 1 for ModularCurve.eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/39c8b429-4981-5a61-8c3a-dbedca759853

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes

set_option autoImplicit false

open ModularCurve AlgebraicCurve

private theorem smul_mem_rational (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p),
      t • z ∈ eisensteinQuotientRational p (heckeModuleBar p) := by
  letI := heckeModuleBar p
  haveI := smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm
  rintro t z ⟨x, hx, rfl⟩
  refine ⟨t • x, ?_, ?_⟩
  · intro σ
    have h := (eisensteinKernelSubmodule p (heckeModuleBar p)).smul_mem t (hx σ)
    rwa [smul_sub, ← smul_comm σ t x] at h
  · rfl

private theorem smul_mem_closure_rational (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
      t • w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro t w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure (smul_mem_rational p hcomm t x hx)
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

private theorem span_le_closure (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ w ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
      w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => exact AddSubgroup.add_mem _ hx hy
  | smul t x _ hx => exact smul_mem_closure_rational p hcomm t x hx

private theorem addGroup_fg_of_le {A : Type*} [AddCommGroup A] {H K : AddSubgroup A}
    (hHK : H ≤ K) (hK : AddGroup.FG ↥K) : AddGroup.FG ↥H := by
  haveI : Module.Finite ℤ ↥K := Module.Finite.iff_addGroup_fg.mpr hK
  haveI : AddGroup.FG ↥(H.addSubgroupOf K) := by
    rw [AddGroup.fg_iff_addSubgroup_fg, ← AddSubgroup.toIntSubmodule_toAddSubgroup (H.addSubgroupOf K),
      ← Submodule.fg_iff_addSubgroup_fg]
    exact IsNoetherian.noetherian _
  exact AddGroup.fg_of_surjective (f := (AddSubgroup.addSubgroupOfEquivOfLe hHK).toAddMonoidHom)
    (AddSubgroup.addSubgroupOfEquivOfLe hHK).surjective

section Generic

open Pointwise

variable {S : Type*} [CommRing S]

private theorem eq_of_le_of_index_eq {A : Type*} [AddCommGroup A] {H K : AddSubgroup A}
    [H.FiniteIndex] (hle : H ≤ K) (heq : H.index = K.index) : H = K := by
  rcases eq_or_lt_of_le hle with h | h
  · exact h
  · exact absurd heq (ne_of_gt (AddSubgroup.index_strictAnti h))

private def zsmulRange (A : Type*) [AddCommGroup A] (k : ℤ) : AddSubgroup A :=
  ((k • (AddMonoidHom.id A : A →+ A)).range : AddSubgroup A)

private theorem mem_zsmulRange {A : Type*} [AddCommGroup A] (k : ℤ) (y : A) :
    y ∈ zsmulRange A k ↔ ∃ x : A, k • x = y :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩⟩

private theorem exists_pow_smul_sub_mem (N : Type*) [AddCommGroup N] [Module S N] [AddGroup.FG N]
    (k : ℕ) (hk : k ≠ 0) (s : S) :
    ∃ a d : ℕ, ∀ n : N,
      s ^ a • (s ^ (d + 1) • n) - s ^ a • n ∈ (nsmulAddMonoidHom k : N →+ N).range := by
  set KN : AddSubgroup N := (nsmulAddMonoidHom k : N →+ N).range
  haveI : KN.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg N hk
  obtain ⟨G, hG⟩ := AddGroup.fg_def.mp ‹AddGroup.FG N›
  obtain ⟨a, b, hab, hF⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => fun g : ↥G => (QuotientAddGroup.mk (s ^ i • (g : N)) : N ⧸ KN))

  have key : ∀ {a b : ℕ}, a < b →
      ((fun g : ↥G => (QuotientAddGroup.mk (s ^ a • (g : N)) : N ⧸ KN)) =
        fun g : ↥G => (QuotientAddGroup.mk (s ^ b • (g : N)) : N ⧸ KN)) →
      ∃ a d : ℕ, ∀ n : N, s ^ a • (s ^ (d + 1) • n) - s ^ a • n ∈ KN := by
    intro a b hlt hfun
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨a, d, ?_⟩

    let D : N →+ N :=
      DistribSMul.toAddMonoidHom N (s ^ a * s ^ (d + 1)) - DistribSMul.toAddMonoidHom N (s ^ a)
    have hD : ∀ n : N, D n = s ^ a • (s ^ (d + 1) • n) - s ^ a • n := by
      intro n
      simp only [D, AddMonoidHom.sub_apply, DistribSMul.toAddMonoidHom_apply, mul_smul]
    have hgen : (G : Set N) ⊆ KN.comap D := by
      intro g hg
      have h1 := congrFun hfun ⟨g, hg⟩
      simp only at h1
      rw [SetLike.mem_coe, AddSubgroup.mem_comap, hD]
      have h2 : -(s ^ a • g) + s ^ (a + d + 1) • g ∈ KN := QuotientAddGroup.eq.mp h1
      rwa [neg_add_eq_sub, show a + d + 1 = a + (d + 1) from by ring, pow_add, mul_smul] at h2
    have hall : (⊤ : AddSubgroup N) ≤ KN.comap D := by
      rw [← hG]
      exact (AddSubgroup.closure_le _).mpr hgen
    intro n
    have := hall (AddSubgroup.mem_top n)
    rwa [AddSubgroup.mem_comap, hD] at this
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact key h hF
  · exact key h hF.symm

private theorem finiteIndex_range_zsmul_localizedModule (W : Submonoid S) (N : Type*) [AddCommGroup N]
    [Module S N] [AddGroup.FG N] (k : ℕ) (hk : k ≠ 0) :
    (zsmulRange (LocalizedModule W N) ((k : ℕ) : ℤ)).FiniteIndex := by
  set L := LocalizedModule W N
  set R : AddSubgroup L := zsmulRange L ((k : ℕ) : ℤ) with hRdef
  set KN : AddSubgroup N := (nsmulAddMonoidHom k : N →+ N).range
  haveI : KN.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg N hk
  have memR : ∀ y : L, ((k : ℕ) : ℤ) • y ∈ R := fun y => (mem_zsmulRange _ _).mpr ⟨y, rfl⟩
  let ι : N →+ L := (LocalizedModule.mkLinearMap W N).toAddMonoidHom
  have hι : ∀ n : N, ι n = LocalizedModule.mk n 1 := fun n => rfl
  have hKR : KN ≤ R.comap ι := by
    rintro _ ⟨n, rfl⟩
    rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, map_nsmul, ← natCast_zsmul]
    exact memR _
  let χ : N ⧸ KN →+ L ⧸ R := QuotientAddGroup.map KN R ι hKR
  have hχ : Function.Surjective χ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    induction y using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨a, d, hfit⟩ := exists_pow_smul_sub_mem N k hk (s : S)
      obtain ⟨n'', hn''⟩ := hfit n
      rw [nsmulAddMonoidHom_apply] at hn''
      refine ⟨QuotientAddGroup.mk ((s : S) ^ d • n), ?_⟩
      show χ (QuotientAddGroup.mk ((s : S) ^ d • n)) = QuotientAddGroup.mk (LocalizedModule.mk n s)
      rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq, hι]

      have hmem : (s : S) ^ a * (s : S) ∈ W := W.mul_mem (pow_mem s.2 a) s.2
      have heq : -(LocalizedModule.mk ((s : S) ^ d • n) 1 : L) + LocalizedModule.mk n s
          = ((k : ℕ) : ℤ) • LocalizedModule.mk (-n'') ⟨(s : S) ^ a * (s : S), hmem⟩ := by
        rw [← LocalizedModule.mk_neg, LocalizedModule.mk_add_mk, ← Int.cast_smul_eq_zsmul S,
          LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Submonoid.coe_one, one_mul,
          Int.cast_natCast, Nat.cast_smul_eq_nsmul, smul_neg]
        rw [hn'']
        simp only [smul_sub, smul_neg, neg_sub, smul_smul]
        module
      rw [heq]
      exact memR _
  haveI : Finite (L ⧸ R) := Finite.of_surjective χ hχ
  exact AddSubgroup.finiteIndex_of_finite_quotient

private theorem stabilizes_of_localized_index_le (P : Ideal S) [P.IsPrime] (hP : P.IsMaximal)
    {E : Type*} [AddCommGroup E] [Module S E] (M : Submodule S E) [AddGroup.FG ↥M]
    (q : ℕ) (hq : 1 < q) (hqP : (q : S) ∈ P)
    (hC : ∃ C : ℕ, ∀ m : ℕ, (zsmulRange (LocalizedModule P.primeCompl ↥M) ((q : ℤ) ^ m)).index ≤ C) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → P ^ m • M = P ^ m₀ • M := by
  classical
  set W := P.primeCompl
  set L := LocalizedModule W ↥M
  have hq0 : q ≠ 0 := by omega

  let Rm : ℕ → AddSubgroup L := fun m => zsmulRange L ((q : ℤ) ^ m)
  have hRm : ∀ m, Rm m = zsmulRange L (((q ^ m : ℕ) : ℤ)) := by
    intro m
    simp only [Rm, Nat.cast_pow]
  have hFI : ∀ m, (Rm m).FiniteIndex := by
    intro m
    rw [hRm]
    exact finiteIndex_range_zsmul_localizedModule W ↥M (q ^ m) (pow_ne_zero m hq0)
  have memRm : ∀ (m : ℕ) (y : L), ((q : ℤ) ^ m) • y ∈ Rm m := fun m y =>
    (mem_zsmulRange _ _).mpr ⟨y, rfl⟩
  have hchain : ∀ m : ℕ, Rm (m + 1) ≤ Rm m := by
    intro m z hz
    obtain ⟨y, rfl⟩ := (mem_zsmulRange _ _).mp hz
    refine (mem_zsmulRange _ _).mpr ⟨(q : ℤ) • y, ?_⟩
    rw [smul_smul, ← pow_succ]
  obtain ⟨C, hC⟩ := hC

  obtain ⟨a, ha⟩ : ∃ a : ℕ, Rm (a + 1) = Rm a := by
    by_contra hne
    push Not at hne
    have hstrict : StrictMono (fun m => (Rm m).index) := by
      apply strictMono_nat_of_lt_succ
      intro m
      haveI := hFI (m + 1)
      have hle := AddSubgroup.index_antitone (hchain m)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (eq_of_le_of_index_eq (hchain m) h.symm) (hne m)
    have h1 : C + 1 ≤ (Rm (C + 1)).index := hstrict.le_apply
    have h2 := hC (C + 1)
    exact absurd (le_trans h1 h2) (by omega)

  obtain ⟨G, hG⟩ := AddGroup.fg_def.mp ‹AddGroup.FG ↥M›
  have hgen : ∀ g : ↥M, ∃ u : S, u ∈ W ∧
      u • ((q : S) ^ a • (g : E)) ∈ (Ideal.span {(q : S) ^ (a + 1)} • M : Submodule S E) := by
    intro g
    have hmem : ((q : ℤ) ^ a) • (LocalizedModule.mk g 1 : L) ∈ Rm (a + 1) := by
      rw [ha]; exact memRm a _
    obtain ⟨y, hy⟩ := (mem_zsmulRange _ _).mp hmem
    induction y using LocalizedModule.induction_on with
    | h n s =>
      rw [← Int.cast_smul_eq_zsmul S, ← Int.cast_smul_eq_zsmul S ((q : ℤ) ^ a),
        LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨v, hv⟩ := hy

      have hvE := congrArg Subtype.val hv
      simp only [one_smul, Submonoid.smul_def, Submodule.coe_smul, Int.cast_pow, Int.cast_natCast,
        smul_smul] at hvE

      refine ⟨(v : S) * (s : S), W.mul_mem v.2 s.2, ?_⟩
      have : ((v : S) * (s : S)) • ((q : S) ^ a • (g : E)) = (q : S) ^ (a + 1) • ((v : S) • (n : E)) := by
        rw [smul_smul, smul_smul]
        have e1 : ((v : S) * (s : S) * (q : S) ^ a) • (g : E) = ((v : S) * ((q : S) ^ (a + 1))) • (n : E) := by
          convert hvE.symm using 2 <;> ring
        rw [e1]
        congr 1
        ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (M.smul_mem _ n.2)
  choose uf hufW hufQ using hgen
  set u : S := ∏ g ∈ G, uf g with hu
  have huW : u ∈ W := Submonoid.prod_mem _ (fun g _ => hufW g)
  have huP : u ∉ P := huW

  have hstep : ∀ x : ↥M,
      u • ((q : S) ^ a • (x : E)) ∈ (Ideal.span {(q : S) ^ (a + 1)} • M : Submodule S E) := by
    intro x
    have hx : x ∈ AddSubgroup.closure (G : Set ↥M) := by rw [hG]; exact AddSubgroup.mem_top x
    induction hx using AddSubgroup.closure_induction with
    | mem g hg =>
      rw [hu, ← Finset.prod_erase_mul G uf hg, mul_smul]
      exact Submodule.smul_mem _ _ (hufQ g)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Submodule.coe_add, smul_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | neg x _ hx =>
      rw [Submodule.coe_neg, smul_neg, smul_neg]
      exact Submodule.neg_mem _ hx

  set Nq : Submodule S E := Ideal.span {(q : S) ^ a} • M with hNq
  have hNq_le_M : Nq ≤ M := Submodule.smul_le_right
  have hNP : Nq ≤ P • Nq := by
    intro z hz
    have hz' : z ∈ ((q : S) ^ a • M : Submodule S E) := by
      rw [← Submodule.ideal_span_singleton_smul]; exact hz
    obtain ⟨x, hxM, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz'
    have h1 : u • ((q : S) ^ a • x) ∈ P • Nq := by
      have h2 := hstep ⟨x, hxM⟩
      simp only [] at h2
      rw [Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, hyM, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
      rw [← hy, pow_succ, mul_comm, mul_smul]
      refine Submodule.smul_mem_smul hqP ?_
      rw [hNq, Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hyM
    obtain ⟨t, π, hπ, htπ⟩ := hP.exists_inv huP
    have hz1 : (q : S) ^ a • x ∈ Nq := by
      rw [hNq, Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hxM
    have : (q : S) ^ a • x = t • (u • ((q : S) ^ a • x)) + π • ((q : S) ^ a • x) := by
      rw [smul_smul, ← add_smul, htπ, one_smul]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem_smul hπ hz1)

  have hNPk : ∀ k : ℕ, Nq ≤ P ^ k • M := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact hNq_le_M
    | succ k ih =>
      calc Nq ≤ P • Nq := hNP
        _ ≤ P • (P ^ k • M) := Submodule.smul_mono le_rfl ih
        _ = P ^ (k + 1) • M := by rw [← Submodule.mul_smul, ← pow_succ']

  let toM : Submodule S E → AddSubgroup ↥M := fun X => X.toAddSubgroup.addSubgroupOf M.toAddSubgroup
  have toM_mono : ∀ {X Y : Submodule S E}, X ≤ Y → toM X ≤ toM Y := by
    intro X Y hXY z hz
    exact hXY hz
  haveI hNqFI : (toM Nq).FiniteIndex := by
    haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg ↥M (pow_ne_zero a hq0 : q ^ a ≠ 0)
    refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (q ^ a) : ↥M →+ ↥M).range) ?_
    rintro _ ⟨y, rfl⟩
    show (((q ^ a) • y : ↥M) : E) ∈ Nq
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul S, Nat.cast_pow, hNq,
      Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ y.2
  let f : ℕ → ℕ := fun m => (toM (P ^ m • M)).index
  have hFIm : ∀ m, (toM (P ^ m • M)).FiniteIndex := fun m =>
    AddSubgroup.finiteIndex_of_le (toM_mono (hNPk m))
  have hf_le : ∀ m, f m ≤ (toM Nq).index := fun m =>
    AddSubgroup.index_antitone (toM_mono (hNPk m))
  have hanti : ∀ m, toM (P ^ (m + 1) • M) ≤ toM (P ^ m • M) := fun m =>
    toM_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m)))
  have hf_mono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro m
    haveI := hFIm (m + 1)
    exact AddSubgroup.index_antitone (hanti m)
  have hbdd : BddAbove (Set.range f) := ⟨(toM Nq).index, by rintro _ ⟨m, rfl⟩; exact hf_le m⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, f m₀ = sSup (Set.range f) := by
    have := Nat.sSup_mem (Set.range_nonempty f) hbdd
    obtain ⟨m₀, h⟩ := this
    exact ⟨m₀, h⟩
  refine ⟨m₀, fun m hm => ?_⟩
  have hle_sub : toM (P ^ m • M) ≤ toM (P ^ m₀ • M) :=
    toM_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hm))
  have hidx : (toM (P ^ m • M)).index = (toM (P ^ m₀ • M)).index := by
    apply le_antisymm
    · show f m ≤ f m₀
      rw [hm₀]; exact le_csSup hbdd (Set.mem_range_self m)
    · exact hf_mono hm
  haveI := hFIm m
  have heq : toM (P ^ m • M) = toM (P ^ m₀ • M) := eq_of_le_of_index_eq hle_sub hidx
  have heq' : (P ^ m • M).toAddSubgroup ⊓ M.toAddSubgroup = (P ^ m₀ • M).toAddSubgroup ⊓ M.toAddSubgroup :=
    AddSubgroup.addSubgroupOf_inj.mp heq
  rw [inf_eq_left.mpr (show (P ^ m • M).toAddSubgroup ≤ M.toAddSubgroup from Submodule.smul_le_right),
    inf_eq_left.mpr (show (P ^ m₀ • M).toAddSubgroup ≤ M.toAddSubgroup from Submodule.smul_le_right)] at heq'
  exact Submodule.toAddSubgroup_injective heq'

end Generic

set_option maxHeartbeats 3200000 in
theorem solution (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime]
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (R : ∀ m : ℕ, JKummerRow q m (eisensteinQuotientRationalLocalized p q))
    (hA1 : ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ m : ℕ,
      letI := (R m).instH1Jtors
      (@AddMonoidHom.range (eisensteinQuotientRationalLocalized p q) _
          (eisensteinQuotientRationalLocalized p q) _
          ((q : ℤ) ^ m • AddMonoidHom.id (eisensteinQuotientRationalLocalized p q))).index ≤ c₀ * Nat.card (R m).H1Jtors)
    (hA2 : ∃ Kb : ℕ, ∀ m : ℕ,
      letI := (R m).instH1Jtors
      Nat.card (R m).H1Jtors ≤ Kb) :
    letI := heckeModuleBar p
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (eisensteinMaximalIdeal p q ^ m •
          Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) =
        (eisensteinMaximalIdeal p q ^ m₀ •
          Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) := by
  letI := heckeModuleBar p
  have hq : q.Prime := Fact.out
  haveI hfgspan : AddGroup.FG
      ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) :=
    addGroup_fg_of_le
      (H := (Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))).toAddSubgroup)
      (fun w hw => span_le_closure p hcomm w hw) hfgc

  have hsurj : Function.Surjective (eisensteinEval p) := fun n =>
    ⟨MvPolynomial.C n, by simp [eisensteinEval]⟩
  haveI : (Ideal.span {(q : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq))
      (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
  have hP : (eisensteinMaximalIdeal p q).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (eisensteinEval p) hsurj

  refine stabilizes_of_localized_index_le (eisensteinMaximalIdeal p q) hP
    (Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) q hq.one_lt
    (natCast_mem_eisensteinMaximalIdeal p q) ?_
  obtain ⟨c₀, -, h1⟩ := hA1
  obtain ⟨Kb, h2⟩ := hA2
  refine ⟨c₀ * Kb, fun m => ?_⟩
  have h := (h1 m).trans (Nat.mul_le_mul_left c₀ (h2 m))
  unfold zsmulRange
  convert h using 3
  all_goals first | rfl | (ext x; simp)

end S_ModularCurve_eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes
end P2MW
export P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes (solution)
