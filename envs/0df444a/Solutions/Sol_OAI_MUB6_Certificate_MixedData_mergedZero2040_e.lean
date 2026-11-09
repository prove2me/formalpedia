-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero2040_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:23:51.595121+00:00
-- url     : https://prove2.me/submissions/511c7ddb-8c2a-43cf-9ab3-400d8a9b7857

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E063
import Definitions.Def_OAIQ106E183
import Definitions.Def_OAIQ106E077

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1966 : merged1966 = Integer.Sparse.merge (Integer.Sparse.scale (361285066742140800) (sourceRows 1969)) (Integer.Sparse.scale (40885950873600) (sourceRows 1970)) := by decide +kernel

theorem mergedZero1966 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1966 x = 0 := by
  rw [mergeCheck1966, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1967 : merged1967 = Integer.Sparse.merge (Integer.Sparse.scale (-776288778239213568000) (sourceRows 1971)) (Integer.Sparse.scale (2508760427018065920) (sourceRows 1972)) := by decide +kernel

theorem mergedZero1967 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1967 x = 0 := by
  rw [mergeCheck1967, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1968 : merged1968 = Integer.Sparse.merge merged1966 merged1967 := by decide +kernel

theorem mergedZero1968 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1968 x = 0 := by
  rw [mergeCheck1968, Integer.Sparse.eval_merge]
  rw [mergedZero1966 x h, mergedZero1967 x h]
  simp only [add_zero]

theorem mergeCheck1969 : merged1969 = Integer.Sparse.merge (Integer.Sparse.scale (-776258527427905536000) (sourceRows 1973)) (Integer.Sparse.scale (-3638677959893975040000) (sourceRows 1974)) := by decide +kernel

theorem mergedZero1969 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1969 x = 0 := by
  rw [mergeCheck1969, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1970 : merged1970 = Integer.Sparse.merge (Integer.Sparse.scale (54099605952000) (sourceRows 1976)) (Integer.Sparse.scale (1883369556620697600) (sourceRows 1977)) := by decide +kernel

theorem mergedZero1970 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1970 x = 0 := by
  rw [mergeCheck1970, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1971 : merged1971 = Integer.Sparse.merge (Integer.Sparse.scale (4939987154532433920000) (sourceRows 1975)) merged1970 := by decide +kernel

theorem mergedZero1971 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1971 x = 0 := by
  rw [mergeCheck1971, Integer.Sparse.eval_merge]
  rw [mergedZero1970 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1972 : merged1972 = Integer.Sparse.merge merged1969 merged1971 := by decide +kernel

theorem mergedZero1972 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1972 x = 0 := by
  rw [mergeCheck1972, Integer.Sparse.eval_merge]
  rw [mergedZero1969 x h, mergedZero1971 x h]
  simp only [add_zero]

theorem mergeCheck1973 : merged1973 = Integer.Sparse.merge merged1968 merged1972 := by decide +kernel

theorem mergedZero1973 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1973 x = 0 := by
  rw [mergeCheck1973, Integer.Sparse.eval_merge]
  rw [mergedZero1968 x h, mergedZero1972 x h]
  simp only [add_zero]

theorem mergeCheck1974 : merged1974 = Integer.Sparse.merge (Integer.Sparse.scale (6010686259200) (sourceRows 1978)) (Integer.Sparse.scale (29344377410039804313600) (sourceRows 1979)) := by decide +kernel

theorem mergedZero1974 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1974 x = 0 := by
  rw [mergeCheck1974, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1975 : merged1975 = Integer.Sparse.merge (Integer.Sparse.scale (-110557376544964608000) (sourceRows 1981)) (Integer.Sparse.scale (-27929844730253768601600) (sourceRows 1982)) := by decide +kernel

theorem mergedZero1975 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1975 x = 0 := by
  rw [mergeCheck1975, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1976 : merged1976 = Integer.Sparse.merge (Integer.Sparse.scale (-110562279626244096000) (sourceRows 1980)) merged1975 := by decide +kernel

theorem mergedZero1976 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1976 x = 0 := by
  rw [mergeCheck1976, Integer.Sparse.eval_merge]
  rw [mergedZero1975 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1977 : merged1977 = Integer.Sparse.merge merged1974 merged1976 := by decide +kernel

theorem mergedZero1977 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1977 x = 0 := by
  rw [mergeCheck1977, Integer.Sparse.eval_merge]
  rw [mergedZero1974 x h, mergedZero1976 x h]
  simp only [add_zero]

theorem mergeCheck1978 : merged1978 = Integer.Sparse.merge (Integer.Sparse.scale (-27049802976000) (sourceRows 1983)) (Integer.Sparse.scale (6758102853323587584000) (sourceRows 1984)) := by decide +kernel

theorem mergedZero1978 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1978 x = 0 := by
  rw [mergeCheck1978, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1979 : merged1979 = Integer.Sparse.merge (Integer.Sparse.scale (6758085910942937088000) (sourceRows 1986)) (Integer.Sparse.scale (11342298116688247296000) (sourceRows 1987)) := by decide +kernel

theorem mergedZero1979 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1979 x = 0 := by
  rw [mergeCheck1979, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1980 : merged1980 = Integer.Sparse.merge (Integer.Sparse.scale (-9146502462499557120) (sourceRows 1985)) merged1979 := by decide +kernel

theorem mergedZero1980 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1980 x = 0 := by
  rw [mergeCheck1980, Integer.Sparse.eval_merge]
  rw [mergedZero1979 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1981 : merged1981 = Integer.Sparse.merge merged1978 merged1980 := by decide +kernel

theorem mergedZero1981 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1981 x = 0 := by
  rw [mergeCheck1981, Integer.Sparse.eval_merge]
  rw [mergedZero1978 x h, mergedZero1980 x h]
  simp only [add_zero]

theorem mergeCheck1982 : merged1982 = Integer.Sparse.merge merged1977 merged1981 := by decide +kernel

theorem mergedZero1982 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1982 x = 0 := by
  rw [mergeCheck1982, Integer.Sparse.eval_merge]
  rw [mergedZero1977 x h, mergedZero1981 x h]
  simp only [add_zero]

theorem mergeCheck1983 : merged1983 = Integer.Sparse.merge merged1973 merged1982 := by decide +kernel

theorem mergedZero1983 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1983 x = 0 := by
  rw [mergeCheck1983, Integer.Sparse.eval_merge]
  rw [mergedZero1973 x h, mergedZero1982 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1984 : merged1984 = Integer.Sparse.merge (Integer.Sparse.scale (-27049802976000) (sourceRows 1988)) (Integer.Sparse.scale (86593735065600) (sourceRows 1989)) := by decide +kernel

theorem mergedZero1984 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1984 x = 0 := by
  rw [mergeCheck1984, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1985 : merged1985 = Integer.Sparse.merge (Integer.Sparse.scale (5272133504530120704000) (sourceRows 1990)) (Integer.Sparse.scale (-5972406013316655360) (sourceRows 1991)) := by decide +kernel

theorem mergedZero1985 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1985 x = 0 := by
  rw [mergeCheck1985, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1986 : merged1986 = Integer.Sparse.merge merged1984 merged1985 := by decide +kernel

theorem mergedZero1986 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1986 x = 0 := by
  rw [mergeCheck1986, Integer.Sparse.eval_merge]
  rw [mergedZero1984 x h, mergedZero1985 x h]
  simp only [add_zero]

theorem mergeCheck1987 : merged1987 = Integer.Sparse.merge (Integer.Sparse.scale (5272090134188967936000) (sourceRows 1992)) (Integer.Sparse.scale (54099605952000) (sourceRows 1993)) := by decide +kernel

theorem mergedZero1987 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1987 x = 0 := by
  rw [mergeCheck1987, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1988 : merged1988 = Integer.Sparse.merge (Integer.Sparse.scale (9567746061081772032000) (sourceRows 1995)) (Integer.Sparse.scale (9567766317456764928000) (sourceRows 1996)) := by decide +kernel

theorem mergedZero1988 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1988 x = 0 := by
  rw [mergeCheck1988, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1989 : merged1989 = Integer.Sparse.merge (Integer.Sparse.scale (28864578355200) (sourceRows 1994)) merged1988 := by decide +kernel

theorem mergedZero1989 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1989 x = 0 := by
  rw [mergeCheck1989, Integer.Sparse.eval_merge]
  rw [mergedZero1988 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1990 : merged1990 = Integer.Sparse.merge merged1987 merged1989 := by decide +kernel

theorem mergedZero1990 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1990 x = 0 := by
  rw [mergeCheck1990, Integer.Sparse.eval_merge]
  rw [mergedZero1987 x h, mergedZero1989 x h]
  simp only [add_zero]

theorem mergeCheck1991 : merged1991 = Integer.Sparse.merge merged1986 merged1990 := by decide +kernel

theorem mergedZero1991 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1991 x = 0 := by
  rw [mergeCheck1991, Integer.Sparse.eval_merge]
  rw [mergedZero1986 x h, mergedZero1990 x h]
  simp only [add_zero]

theorem mergeCheck1992 : merged1992 = Integer.Sparse.merge (Integer.Sparse.scale (4909473399152306073600) (sourceRows 1997)) (Integer.Sparse.scale (-28864578355200) (sourceRows 1998)) := by decide +kernel

theorem mergedZero1992 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1992 x = 0 := by
  rw [mergeCheck1992, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1993 : merged1993 = Integer.Sparse.merge (Integer.Sparse.scale (-6871211421095411712000) (sourceRows 2000)) (Integer.Sparse.scale (256475792744781926400) (sourceRows 2001)) := by decide +kernel

theorem mergedZero1993 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1993 x = 0 := by
  rw [mergeCheck1993, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1994 : merged1994 = Integer.Sparse.merge (Integer.Sparse.scale (-6871315395363471360000) (sourceRows 1999)) merged1993 := by decide +kernel

theorem mergedZero1994 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1994 x = 0 := by
  rw [mergeCheck1994, Integer.Sparse.eval_merge]
  rw [mergedZero1993 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1995 : merged1995 = Integer.Sparse.merge merged1992 merged1994 := by decide +kernel

theorem mergedZero1995 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1995 x = 0 := by
  rw [mergeCheck1995, Integer.Sparse.eval_merge]
  rw [mergedZero1992 x h, mergedZero1994 x h]
  simp only [add_zero]

theorem mergeCheck1996 : merged1996 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 2002)) (Integer.Sparse.scale (-28864578355200) (sourceRows 2003)) := by decide +kernel

theorem mergedZero1996 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1996 x = 0 := by
  rw [mergeCheck1996, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1997 : merged1997 = Integer.Sparse.merge (Integer.Sparse.scale (1226372419657728000) (sourceRows 2005)) (Integer.Sparse.scale (-946634569699295232000) (sourceRows 2006)) := by decide +kernel

theorem mergedZero1997 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1997 x = 0 := by
  rw [mergeCheck1997, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1998 : merged1998 = Integer.Sparse.merge (Integer.Sparse.scale (-95607372930048000) (sourceRows 2004)) merged1997 := by decide +kernel

theorem mergedZero1998 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1998 x = 0 := by
  rw [mergeCheck1998, Integer.Sparse.eval_merge]
  rw [mergedZero1997 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1999 : merged1999 = Integer.Sparse.merge merged1996 merged1998 := by decide +kernel

theorem mergedZero1999 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1999 x = 0 := by
  rw [mergeCheck1999, Integer.Sparse.eval_merge]
  rw [mergedZero1996 x h, mergedZero1998 x h]
  simp only [add_zero]

theorem mergeCheck2000 : merged2000 = Integer.Sparse.merge merged1995 merged1999 := by decide +kernel

theorem mergedZero2000 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2000 x = 0 := by
  rw [mergeCheck2000, Integer.Sparse.eval_merge]
  rw [mergedZero1995 x h, mergedZero1999 x h]
  simp only [add_zero]

theorem mergeCheck2001 : merged2001 = Integer.Sparse.merge merged1991 merged2000 := by decide +kernel

theorem mergedZero2001 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2001 x = 0 := by
  rw [mergeCheck2001, Integer.Sparse.eval_merge]
  rw [mergedZero1991 x h, mergedZero2000 x h]
  simp only [add_zero]

theorem mergeCheck2002 : merged2002 = Integer.Sparse.merge merged1983 merged2001 := by decide +kernel

theorem mergedZero2002 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2002 x = 0 := by
  rw [mergeCheck2002, Integer.Sparse.eval_merge]
  rw [mergedZero1983 x h, mergedZero2001 x h]
  simp only [add_zero]

theorem mergeCheck2003 : merged2003 = Integer.Sparse.merge (Integer.Sparse.scale (-946627287878651904000) (sourceRows 2007)) (Integer.Sparse.scale (-12097352111278075084800) (sourceRows 2008)) := by decide +kernel

theorem mergedZero2003 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2003 x = 0 := by
  rw [mergeCheck2003, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2004 : merged2004 = Integer.Sparse.merge (Integer.Sparse.scale (12097352111278075084800) (sourceRows 2009)) (Integer.Sparse.scale (-1171014574012416000) (sourceRows 2010)) := by decide +kernel

theorem mergedZero2004 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2004 x = 0 := by
  rw [mergeCheck2004, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2005 : merged2005 = Integer.Sparse.merge merged2003 merged2004 := by decide +kernel

theorem mergedZero2005 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2005 x = 0 := by
  rw [mergeCheck2005, Integer.Sparse.eval_merge]
  rw [mergedZero2003 x h, mergedZero2004 x h]
  simp only [add_zero]

theorem mergeCheck2006 : merged2006 = Integer.Sparse.merge (Integer.Sparse.scale (350565446568960000) (sourceRows 2011)) (Integer.Sparse.scale (-37298392435261440) (sourceRows 2012)) := by decide +kernel

theorem mergedZero2006 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2006 x = 0 := by
  rw [mergeCheck2006, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2007 : merged2007 = Integer.Sparse.merge (Integer.Sparse.scale (-110647971302400) (sourceRows 2014)) (Integer.Sparse.scale (-78823777536000) (sourceRows 2015)) := by decide +kernel

theorem mergedZero2007 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2007 x = 0 := by
  rw [mergeCheck2007, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2008 : merged2008 = Integer.Sparse.merge (Integer.Sparse.scale (-6491776759738608844800) (sourceRows 2013)) merged2007 := by decide +kernel

theorem mergedZero2008 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2008 x = 0 := by
  rw [mergeCheck2008, Integer.Sparse.eval_merge]
  rw [mergedZero2007 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2009 : merged2009 = Integer.Sparse.merge merged2006 merged2008 := by decide +kernel

theorem mergedZero2009 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2009 x = 0 := by
  rw [mergeCheck2009, Integer.Sparse.eval_merge]
  rw [mergedZero2006 x h, mergedZero2008 x h]
  simp only [add_zero]

theorem mergeCheck2010 : merged2010 = Integer.Sparse.merge merged2005 merged2009 := by decide +kernel

theorem mergedZero2010 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2010 x = 0 := by
  rw [mergeCheck2010, Integer.Sparse.eval_merge]
  rw [mergedZero2005 x h, mergedZero2009 x h]
  simp only [add_zero]

theorem mergeCheck2011 : merged2011 = Integer.Sparse.merge (Integer.Sparse.scale (715114002293784576000) (sourceRows 2016)) (Integer.Sparse.scale (715158314160482304000) (sourceRows 2017)) := by decide +kernel

theorem mergedZero2011 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2011 x = 0 := by
  rw [mergeCheck2011, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2012 : merged2012 = Integer.Sparse.merge (Integer.Sparse.scale (-1004952344161812480000) (sourceRows 2019)) (Integer.Sparse.scale (-1004938408125840384000) (sourceRows 2020)) := by decide +kernel

theorem mergedZero2012 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2012 x = 0 := by
  rw [mergeCheck2012, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2013 : merged2013 = Integer.Sparse.merge (Integer.Sparse.scale (389388921062400) (sourceRows 2018)) merged2012 := by decide +kernel

theorem mergedZero2013 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2013 x = 0 := by
  rw [mergeCheck2013, Integer.Sparse.eval_merge]
  rw [mergedZero2012 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2014 : merged2014 = Integer.Sparse.merge merged2011 merged2013 := by decide +kernel

theorem mergedZero2014 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2014 x = 0 := by
  rw [mergeCheck2014, Integer.Sparse.eval_merge]
  rw [mergedZero2011 x h, mergedZero2013 x h]
  simp only [add_zero]

theorem mergeCheck2015 : merged2015 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 2021)) (Integer.Sparse.scale (6010686259200) (sourceRows 2022)) := by decide +kernel

theorem mergedZero2015 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2015 x = 0 := by
  rw [mergeCheck2015, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2016 : merged2016 = Integer.Sparse.merge (Integer.Sparse.scale (4626754611944951808000) (sourceRows 2024)) (Integer.Sparse.scale (103911676728975360) (sourceRows 2025)) := by decide +kernel

theorem mergedZero2016 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2016 x = 0 := by
  rw [mergeCheck2016, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2017 : merged2017 = Integer.Sparse.merge (Integer.Sparse.scale (4626833136178692096000) (sourceRows 2023)) merged2016 := by decide +kernel

theorem mergedZero2017 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2017 x = 0 := by
  rw [mergeCheck2017, Integer.Sparse.eval_merge]
  rw [mergedZero2016 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2018 : merged2018 = Integer.Sparse.merge merged2015 merged2017 := by decide +kernel

theorem mergedZero2018 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2018 x = 0 := by
  rw [mergeCheck2018, Integer.Sparse.eval_merge]
  rw [mergedZero2015 x h, mergedZero2017 x h]
  simp only [add_zero]

theorem mergeCheck2019 : merged2019 = Integer.Sparse.merge merged2014 merged2018 := by decide +kernel

theorem mergedZero2019 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2019 x = 0 := by
  rw [mergeCheck2019, Integer.Sparse.eval_merge]
  rw [mergedZero2014 x h, mergedZero2018 x h]
  simp only [add_zero]

theorem mergeCheck2020 : merged2020 = Integer.Sparse.merge merged2010 merged2019 := by decide +kernel

theorem mergedZero2020 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2020 x = 0 := by
  rw [mergeCheck2020, Integer.Sparse.eval_merge]
  rw [mergedZero2010 x h, mergedZero2019 x h]
  simp only [add_zero]

theorem mergeCheck2021 : merged2021 = Integer.Sparse.merge (Integer.Sparse.scale (4501291376384409600000) (sourceRows 2026)) (Integer.Sparse.scale (2216831132152627200000) (sourceRows 2027)) := by decide +kernel

theorem mergedZero2021 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2021 x = 0 := by
  rw [mergeCheck2021, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2022 : merged2022 = Integer.Sparse.merge (Integer.Sparse.scale (-2089015568665804800000) (sourceRows 2028)) (Integer.Sparse.scale (2139241300593868800000) (sourceRows 2029)) := by decide +kernel

theorem mergedZero2022 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2022 x = 0 := by
  rw [mergeCheck2022, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2023 : merged2023 = Integer.Sparse.merge merged2021 merged2022 := by decide +kernel

theorem mergedZero2023 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2023 x = 0 := by
  rw [mergeCheck2023, Integer.Sparse.eval_merge]
  rw [mergedZero2021 x h, mergedZero2022 x h]
  simp only [add_zero]

theorem mergeCheck2024 : merged2024 = Integer.Sparse.merge (Integer.Sparse.scale (52429989873604279910400) (sourceRows 2030)) (Integer.Sparse.scale (-65320569921628978790400) (sourceRows 2031)) := by decide +kernel

theorem mergedZero2024 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2024 x = 0 := by
  rw [mergeCheck2024, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2025 : merged2025 = Integer.Sparse.merge (Integer.Sparse.scale (-93142192550400) (sourceRows 2033)) (Integer.Sparse.scale (-6025739588618158080) (sourceRows 2034)) := by decide +kernel

theorem mergedZero2025 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2025 x = 0 := by
  rw [mergeCheck2025, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2026 : merged2026 = Integer.Sparse.merge (Integer.Sparse.scale (39296502354289265971200) (sourceRows 2032)) merged2025 := by decide +kernel

theorem mergedZero2026 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2026 x = 0 := by
  rw [mergeCheck2026, Integer.Sparse.eval_merge]
  rw [mergedZero2025 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2027 : merged2027 = Integer.Sparse.merge merged2024 merged2026 := by decide +kernel

theorem mergedZero2027 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2027 x = 0 := by
  rw [mergeCheck2027, Integer.Sparse.eval_merge]
  rw [mergedZero2024 x h, mergedZero2026 x h]
  simp only [add_zero]

theorem mergeCheck2028 : merged2028 = Integer.Sparse.merge merged2023 merged2027 := by decide +kernel

theorem mergedZero2028 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2028 x = 0 := by
  rw [mergeCheck2028, Integer.Sparse.eval_merge]
  rw [mergedZero2023 x h, mergedZero2027 x h]
  simp only [add_zero]

theorem mergeCheck2029 : merged2029 = Integer.Sparse.merge (Integer.Sparse.scale (-23114468966400) (sourceRows 2035)) (Integer.Sparse.scale (108210322483200) (sourceRows 2036)) := by decide +kernel

theorem mergedZero2029 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2029 x = 0 := by
  rw [mergeCheck2029, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2030 : merged2030 = Integer.Sparse.merge (Integer.Sparse.scale (-29304446976000) (sourceRows 2038)) (Integer.Sparse.scale (3649105010862194688000) (sourceRows 2039)) := by decide +kernel

theorem mergedZero2030 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2030 x = 0 := by
  rw [mergeCheck2030, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2031 : merged2031 = Integer.Sparse.merge (Integer.Sparse.scale (12968050737688945920) (sourceRows 2037)) merged2030 := by decide +kernel

theorem mergedZero2031 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2031 x = 0 := by
  rw [mergeCheck2031, Integer.Sparse.eval_merge]
  rw [mergedZero2030 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2032 : merged2032 = Integer.Sparse.merge merged2029 merged2031 := by decide +kernel

theorem mergedZero2032 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2032 x = 0 := by
  rw [mergeCheck2032, Integer.Sparse.eval_merge]
  rw [mergedZero2029 x h, mergedZero2031 x h]
  simp only [add_zero]

theorem mergeCheck2033 : merged2033 = Integer.Sparse.merge (Integer.Sparse.scale (419246234007552000) (sourceRows 2040)) (Integer.Sparse.scale (3649059263913670656000) (sourceRows 2041)) := by decide +kernel

theorem mergedZero2033 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2033 x = 0 := by
  rw [mergeCheck2033, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2034 : merged2034 = Integer.Sparse.merge (Integer.Sparse.scale (51638369936374816358400) (sourceRows 2043)) (Integer.Sparse.scale (-55014130110282784358400) (sourceRows 2044)) := by decide +kernel

theorem mergedZero2034 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2034 x = 0 := by
  rw [mergeCheck2034, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2035 : merged2035 = Integer.Sparse.merge (Integer.Sparse.scale (13669767438598397952000) (sourceRows 2042)) merged2034 := by decide +kernel

theorem mergedZero2035 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2035 x = 0 := by
  rw [mergeCheck2035, Integer.Sparse.eval_merge]
  rw [mergedZero2034 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2036 : merged2036 = Integer.Sparse.merge merged2033 merged2035 := by decide +kernel

theorem mergedZero2036 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2036 x = 0 := by
  rw [mergeCheck2036, Integer.Sparse.eval_merge]
  rw [mergedZero2033 x h, mergedZero2035 x h]
  simp only [add_zero]

theorem mergeCheck2037 : merged2037 = Integer.Sparse.merge merged2032 merged2036 := by decide +kernel

theorem mergedZero2037 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2037 x = 0 := by
  rw [mergeCheck2037, Integer.Sparse.eval_merge]
  rw [mergedZero2032 x h, mergedZero2036 x h]
  simp only [add_zero]

theorem mergeCheck2038 : merged2038 = Integer.Sparse.merge merged2028 merged2037 := by decide +kernel

theorem mergedZero2038 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2038 x = 0 := by
  rw [mergeCheck2038, Integer.Sparse.eval_merge]
  rw [mergedZero2028 x h, mergedZero2037 x h]
  simp only [add_zero]

theorem mergeCheck2039 : merged2039 = Integer.Sparse.merge merged2020 merged2038 := by decide +kernel

theorem mergedZero2039 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2039 x = 0 := by
  rw [mergeCheck2039, Integer.Sparse.eval_merge]
  rw [mergedZero2020 x h, mergedZero2038 x h]
  simp only [add_zero]

theorem mergeCheck2040 : merged2040 = Integer.Sparse.merge merged2002 merged2039 := by decide +kernel

theorem mergedZero2040_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2040 x = 0 := by
  rw [mergeCheck2040, Integer.Sparse.eval_merge]
  rw [mergedZero2002 x h, mergedZero2039 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero2040_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero2040_e_oai
